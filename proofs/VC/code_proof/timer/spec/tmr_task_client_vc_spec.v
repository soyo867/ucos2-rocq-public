Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_witness_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_iteration_entry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_entry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_adapter_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_call_layout_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_progress_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_source_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_source_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_callback_registry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_progress_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.lib.timer.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import CNotation.
Import ListNotations TimerCallback_C_Rules TimerCallback_C_Rules.Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(** The generated pure prefixes retain the supplied observations.  This
    tactic stops before the spatial predicate, whose resource proof is explicit. *)
Ltac tmr_task_vc_pure :=
  first [assumption | reflexivity | split; tmr_task_vc_pure].
Ltac tmr_task_vc_keep_pure :=
  repeat (split; [solve [tmr_task_vc_pure] |]).

Lemma tmr_task_fields_separated_frame : forall P Q R,
  TmrTaskFieldsRules.derivable1 P Q ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon P R) (TmrTaskFieldsRules.sepcon Q R).
Proof.
  intros P Q R H heap [left_heap [right_heap [Hjoin [HP HR]]]].
  exists left_heap, right_heap; split; [exact Hjoin|].
  split; [apply H; exact HP|exact HR].
Qed.

Lemma tmr_task_fields_separated_right_frame : forall P Q R,
  TmrTaskFieldsRules.derivable1 P Q ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon R P) (TmrTaskFieldsRules.sepcon R Q).
Proof.
  intros P Q R H heap [left_heap [right_heap [Hjoin [HR HP]]]].
  exists left_heap, right_heap; split; [exact Hjoin|].
  split; [exact HR|apply H; exact HP].
Qed.

Lemma tmr_task_fields_signal_post_open : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical local
  sg call mask perr (before : tmr_task_scan_world Application),
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift (tmr_task_unlock_fields_signal_post
        environment critical local sg call mask (tmr_task_kernel before)
        tmr_task_fields_kernel_any))
      (tmr_task_fields_client AppRep perr before))
    (fun heap => exists returned current,
      os_sched_unlock_continuation_return_facts environment critical sg call mask
        (tmr_task_kernel before) tmr_task_fields_kernel_any returned current /\
      os_sched_unlock_fields_return_sources environment critical sg call mask
        (tmr_task_kernel before) returned current /\
      tmr_task_signal_lifetime critical sg (os_sched_call_invocation returned) current /\
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsRules.lift (os_sched_unlock_fields_return_world
          environment local sg returned mask current))
        (tmr_task_fields_client AppRep perr before) heap).
Proof.
  intros Application AppRep environment critical local sg call mask perr before heap
    [owned [client [Hjoin [[returned [current [[[Hfacts Hsources] Hlife] Hworld]]]
      Hclient]]]].
  exists returned, current; split; [exact Hfacts|].
  split; [exact Hsources|]. split; [exact Hlife|].
  exists owned, client; split; [exact Hjoin|]; split; assumption.
Qed.

Lemma tmr_task_fields_lock_post_world : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical local sg
  original mask perr (before : tmr_task_scan_world Application),
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsCallee.lock_post environment critical local sg original mask
        (tmr_task_kernel before) tmr_task_fields_kernel_any)
      (tmr_task_fields_client AppRep perr before))
    (fun heap => exists returned current,
      os_sched_lock_continuation_history environment critical sg original mask
        (tmr_task_kernel before) returned current /\
      kernel_call_normal_return original (tmr_task_kernel before) returned current /\
      (kernel_call_task_source original (tmr_task_kernel before) -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control (tmr_task_kernel before) current /\
      os_sched_lock_fields_return_sources environment critical sg original mask
        (tmr_task_kernel before) returned current /\
      tmr_task_current_fields_owned AppRep environment sg mask perr returned
        (current, tmr_task_application before) heap).
Proof.
  intros Application AppRep environment critical local sg original mask perr before heap
    [kernel [client [Hjoin [Hpost Hclient]]]].
  destruct Hpost as [returned [current [[Hhistory [Hnormal [Hsource [Hcontrol [Hsources Hsafe]]]]] Hclosed]]].
  exists returned, current; split; [exact Hhistory|]. split; [exact Hnormal|].
  split; [exact Hsource|]. split; [exact Hcontrol|]. split; [exact Hsources|].
  exists local, kernel, client; split; [exact Hjoin|]. split; assumption.
Qed.

Lemma tmr_task_unlink_world_preserves_entry_lifetime : forall Application critical sg
  call (before after : tmr_task_scan_world Application) index,
  tmr_task_unlink_world sg before index after ->
  tmr_task_unlock_entry sg call (tmr_task_kernel before) ->
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel before) ->
  tmr_task_unlock_entry sg call (tmr_task_kernel after) /\
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel after).
Proof.
  intros Application critical sg call before after index [timers [Hstep ->]] Hentry Hlife.
  split; [exact Hentry|].
  eapply tmr_task_signal_lifetime_preserved; [exact Hlife|].
  apply tmr_task_timer_update_preserves_signal_identity.
  exact (proj1 (proj2 (proj2 (tmr_task_unlink_service_frame sg (tmr_task_timers before) index timers Hstep)))).
Qed.

Lemma tmr_task_link_world_preserves_entry_lifetime : forall Application critical sg
  call (before after : tmr_task_scan_world Application) index,
  tmr_task_link_world sg before index after ->
  tmr_task_unlock_entry sg call (tmr_task_kernel before) ->
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel before) ->
  tmr_task_unlock_entry sg call (tmr_task_kernel after) /\
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel after).
Proof.
  intros Application critical sg call before after index [timers [Hstep ->]] Hentry Hlife.
  split; [exact Hentry|].
  eapply tmr_task_signal_lifetime_preserved; [exact Hlife|].
  apply tmr_task_timer_update_preserves_signal_identity.
  exact (proj1 (proj2 (proj2 (tmr_task_link_service_frame sg (tmr_task_timers before) index true timers Hstep)))).
Qed.

Lemma tmr_task_complete_world_preserves_entry_lifetime : forall Application critical sg
  call (before after : tmr_task_scan_world Application) index,
  tmr_task_complete_world before index after ->
  tmr_task_unlock_entry sg call (tmr_task_kernel before) ->
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel before) ->
  tmr_task_unlock_entry sg call (tmr_task_kernel after) /\
  tmr_task_signal_lifetime critical sg (os_sched_call_invocation call) (tmr_task_kernel after).
Proof.
  intros Application critical sg call before after index [timers [Hstep ->]] Hentry Hlife.
  split; [exact Hentry|].
  eapply tmr_task_signal_lifetime_preserved; [exact Hlife|].
  apply tmr_task_timer_update_preserves_signal_identity.
  exact (proj1 (proj2 (proj2 (tmr_task_complete_service_frame (tmr_task_timers before) index timers Hstep)))).
Qed.

Lemma tmr_task_dispatch_prepared_preserves_initialized : forall Application sg
  (before after : tmr_task_scan_world Application) index cached,
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_dispatch_prepared sg before index cached after ->
  timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application sg before after index cached Hinit [request [timers [Hstep ->]]].
  change (timer_api_initialized timers).
  unfold timer_api_initialized in *.
  rewrite (timer_expire_dispatch_preserves_initialization_phase sg
    (tmr_task_timers before) index cached request timers Hstep); exact Hinit.
Qed.

Lemma tmr_task_fields_sepcon_mono : forall P Q P' Q',
  TmrTaskFieldsRules.derivable1 P P' -> TmrTaskFieldsRules.derivable1 Q Q' ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon P Q) (TmrTaskFieldsRules.sepcon P' Q').
Proof.
  intros P Q P' Q' HP HQ heap [first [second [Hjoin [Hfirst Hsecond]]]].
  exists first, second; split; [exact Hjoin|]. split; [apply HP|apply HQ]; assumption.
Qed.

Lemma tmr_task_fields_store_ptr_forget : forall pointer value,
  TmrTaskFieldsRules.derivable1 (TmrTaskFieldsRules.store_ptr pointer value)
    (TmrTaskFieldsRules.undef_store_ptr pointer).
Proof.
  intros pointer value [heap environment] Hcell.
  apply (proj2 (TmrTaskFieldsRules.undef_store_ptr_slice environment pointer heap)).
  apply (UCOS2_C_Rules.store_ptr_undef_store_ptr pointer value).
  exact (proj1 (TmrTaskFieldsRules.store_ptr_slice environment pointer value heap) Hcell).
Qed.

Lemma tmr_task_fields_store_ushort_forget : forall pointer value,
  TmrTaskFieldsRules.derivable1 (TmrTaskFieldsRules.store_ushort pointer value)
    (TmrTaskFieldsRules.undef_store_ushort pointer).
Proof.
  intros pointer value [heap environment] Hcell.
  apply (proj2 (TmrTaskFieldsRules.undef_store_ushort_slice environment pointer heap)).
  apply (UCOS2_C_Rules.store_ushort_undef_store_ushort pointer value).
  exact (proj1 (TmrTaskFieldsRules.store_ushort_slice environment pointer value heap) Hcell).
Qed.

Ltac tmr_task_vc_weaken :=
  first [assumption | solve [intros heap Hheap; exact Hheap] |
    apply tmr_task_fields_sepcon_mono; tmr_task_vc_weaken |
    apply tmr_task_fields_store_ptr_forget |
    apply tmr_task_fields_store_ushort_forget].

(** Compose the two actual C updates at an expired timer.  The option
    conversion is justified by the live image of the actual unlink result. *)
Lemma tmr_task_dispatch_prepared_from_updates : forall Application sg
  (before unlinked after : tmr_task_scan_world Application) index image
  unlinked_image cached,
  tmr_task_profile sg -> valid_timer_state sg (tmr_task_timers before) ->
  tmr_unlink_running (tmr_task_timers before) index ->
  tmr_task_fields_image_at before index image ->
  timerTime (tmr_task_timers before) = timerImageMatch image ->
  cached = timerImageNext image ->
  tmr_task_unlink_world sg before index unlinked ->
  tmr_task_fields_image_at unlinked index unlinked_image ->
  ((unsigned_last_nbits (timerImageOption unlinked_image) 32 = 2 /\
      tmr_task_link_world sg unlinked index after) \/
   (unsigned_last_nbits (timerImageOption unlinked_image) 32 <> 2 /\
      tmr_task_complete_world unlinked index after)) ->
  exists call_image,
    tmr_task_dispatch_prepared sg before index cached after /\
    tmr_task_fields_image_at after index call_image.
Proof.
  intros Application sg before unlinked after index image unlinked_image cached
    Hprofile Hvalid [node [Hnode Hrunning]] Himage Hdue Hcached
    [unlinked_timers [Hunlink ->]] Hunlinked_image Hupdated.
  destruct (tmr_task_profile_scan_geometry sg Hprofile) as [_ Hlayout].
  pose proof (timer_unlink_preserves_state_validity sg (tmr_task_timers before)
    index node unlinked_timers Hlayout Hvalid Hnode Hrunning Hunlink) as Hunlinked_valid.
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hunlink)
    as [unlinked_node [found [Hunlinked_node [Hfound Hrest]]]].
  assert (Hunsigned : unsigned_last_nbits (timerImageOption unlinked_image) 32 =
    timerImageOption unlinked_image).
  { eapply tmr_task_used_image_option_unsigned; eassumption. }
  destruct Hupdated as [[Hmode [updated [Hupdate ->]]]|[Hmode [updated [Hupdate ->]]]].
  - rewrite Hunsigned in Hmode.
    change (timer_link sg unlinked_timers index true = Some updated) in Hupdate.
    destruct (timer_link_sets_running_match _ _ _ _ _ Hupdate)
      as [updated_node [call_image [_ [Hcall_image _]]]].
    exists call_image; split; [|exact Hcall_image].
    exists (if Z.eqb call_image.(timerImageCallback) 0 then None else
      Some (call_image.(timerImageCallback), timer_pool_addr sg index,
        call_image.(timerImageArg))), updated; split; [|reflexivity].
    unfold timer_expire_dispatch; rewrite Himage, Hdue, Z.eqb_refl, Hunlink.
    change (timerImages unlinked_timers index = Some unlinked_image) in Hunlinked_image.
    rewrite Hunlinked_image, Hmode; cbn zeta; rewrite Z.eqb_refl, Hupdate, Hcall_image.
    rewrite Hcached; reflexivity.
  - rewrite Hunsigned in Hmode.
    change (timer_complete unlinked_timers index = Some updated) in Hupdate.
    pose proof (timer_complete_target_image_eq _ _ _ _ Hunlinked_image Hupdate) as Hcall_image.
    exists (timer_complete_image unlinked_image); split; [|exact Hcall_image].
    exists (if Z.eqb (timer_complete_image unlinked_image).(timerImageCallback) 0 then None else
      Some ((timer_complete_image unlinked_image).(timerImageCallback), timer_pool_addr sg index,
        (timer_complete_image unlinked_image).(timerImageArg))), updated; split; [|reflexivity].
    unfold timer_expire_dispatch; rewrite Himage, Hdue, Z.eqb_refl, Hunlink.
    change (timerImages unlinked_timers index = Some unlinked_image) in Hunlinked_image.
    rewrite Hunlinked_image; cbn zeta.
    rewrite (proj2 (Z.eqb_neq _ _) Hmode), Hupdate, Hcall_image.
    rewrite Hcached; reflexivity.
Qed.

Lemma tmr_task_callback_domain_from_prepared : forall Application environment critical sg mask
  callback initial_context initial history visited context
  (before after : tmr_task_scan_world Application) cursor index tail future cached image X,
  tmr_task_client_scan_facts environment critical sg mask (tmr_task_framed_effects callback)
    initial_context initial history visited context before cursor X ->
  timerScanRemaining cursor = index :: tail ->
  timer_scan_advance (tmr_task_timers before) cursor = Some future ->
  tmr_task_image_read before index TaskMatchField (timerTime (tmr_task_timers before)) ->
  tmr_task_dispatch_prepared sg before index cached after ->
  tmr_task_fields_image_at after index image -> timerImageCallback image <> 0 ->
  tmr_task_client_callback_domain environment critical sg callback mask initial_context initial
    (timerImageCallback image) (timer_pool_addr sg index) (timerImageArg image) context after /\
  tmr_task_callback_dispatch_domain sg (timerImageCallback image) (timer_pool_addr sg index)
    (timerImageArg image) after.
Proof.
  intros Application environment critical sg mask callback initial_context initial history
    visited context before after cursor index tail future cached image X Hfacts Hremaining
    Hadvance [original [Horiginal Hdue]] [request [timers [Hdispatch ->]]] Himage Hnonnull.
  pose proof (tmr_task_due_dispatch_request_eq sg (tmr_task_timers before) index original
    cached request timers image Horiginal Hdue Hdispatch Himage) as Hrequest.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonnull) in Hrequest; subst request; split.
  - eapply tmr_task_client_callback_domain_from_scan; eassumption.
  - exists before, index, cached, timers; split.
    + unfold tmr_task_client_scan_facts in Hfacts; tauto.
    + split; [exact Hdispatch|reflexivity].
Qed.


(** The following adapters consume the checked clear-status Sem contract
    directly. The old Pend9 adapters above remain unchanged. *)
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_iteration_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Definition tmr_task_client_clear_status_pend_lifted_post environment critical sg call mask pevent timeout perr before X :=
  TmrTaskFieldsRules.lift (tmr_task_client_clear_status_pend_post environment critical sg call mask
    pevent timeout perr before X).

Definition tmr_task_client_clear_status_pend_argument_rest environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.wand (TmrTaskFieldsRules.store_ptr signal_address signal)
    (TmrTaskFieldsRules.lift (tmr_task_client_clear_status_pend_pre environment local critical sg call mask
      signal timeout perr before eid observed X)).

Definition tmr_task_client_clear_status_pend_argument_pre environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.store_ptr signal_address signal)
    (tmr_task_client_clear_status_pend_argument_rest environment local critical sg call mask
      signal timeout perr before eid observed X signal_address).

Lemma tmr_task_client_clear_status_pend_argument_closed : forall environment local critical sg call mask
  signal timeout perr before eid observed X signal_address,
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_clear_status_pend_argument_pre environment local critical sg call mask
      signal timeout perr before eid observed X signal_address)
    (TmrTaskFieldsRules.lift (tmr_task_client_clear_status_pend_pre environment local critical sg call mask
      signal timeout perr before eid observed X)).
Proof.
  intros environment local critical sg call mask signal timeout perr before eid observed X
    signal_address heap [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (Hrest cell heap).
  - exact (TmrTaskFieldsRules.join_comm cell rest heap Hjoin).
  - exact Hcell.
Qed.

Section TmrTaskClientClearStatusPendHeap.
Import UCOS2_C_Rules TmrTaskClientPendHeap.
Local Open Scope sac_scope.
Lemma tmr_task_clear_status_signal_rest_closes_pend : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  tmr_task_client_clear_status_pend_domain critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  tmr_task_client_clear_status_pend_entry sg call before ->
  signal_rest environment local sg call mask perr before |--
  (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
    tmr_task_client_clear_status_pend_pre environment local critical sg call mask
      before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain Hentry.
  apply_sepcon_adjoint.
  assert (Hmerge :
    signal_rest environment local sg call mask perr before **
      sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) |--
    sem_pend_error_cell perr ** TmrTaskFields.tmr_task_fields_context environment local sg call mask before).
  { sep_apply_r_atomic (TmrTaskFieldsHeap.context_merge_read_part environment local sg call mask before
      (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
      (timer_without_signal sg before.(TimerState)) Hen Hinit
      (proj2 (timer_split_merge_signal sg before.(TimerState)))).
    unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!. }
  intros heap Hheap; split.
  - split; [exact Hdomain|]. split; [exact Hentry|].
    unfold sem_pend_client_fields_call_safe, safeExec, safe, StateRelHoare.weakestpre, tmr_task_legacy_any.
    exists (RTrans_Abs before); split.
    + unfold LastSeen; intro state; split; trivial.
    + sets_unfold; intros; exact I.
  - exact (Hmerge heap Hheap).
Qed.

Lemma tmr_task_clear_status_context_split_pend_argument : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  tmr_task_client_clear_status_pend_domain critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  tmr_task_client_clear_status_pend_entry sg call before ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask before ** sem_pend_error_cell perr |--
  sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) **
    (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
      tmr_task_client_clear_status_pend_pre environment local critical sg call mask
        before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain Hentry.
  sep_apply_l_atomic (TmrTaskFieldsHeap.context_split_part environment local sg call mask before
    (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
    (timer_without_signal sg before.(TimerState)) Hen Hinit
    (proj1 (timer_split_merge_signal sg before.(TimerState)))).
  sep_apply_r_atomic (tmr_task_clear_status_signal_rest_closes_pend environment local critical sg call mask perr before
    eid observed Hen Hinit Hdomain Hentry).
  unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!.
Qed.

End TmrTaskClientClearStatusPendHeap.

Lemma tmr_task_client_clear_status_pend_argument_from_owner : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical sg call mask perr
  (world : tmr_task_scan_world Application) eid observed,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers world) ->
  tmr_task_client_clear_status_pend_domain critical sg call
    (tmr_task_timers world).(timerSignalSem) (tmr_task_kernel world) eid observed ->
  tmr_task_client_clear_status_pend_entry sg call (tmr_task_kernel world) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (fun heap => exists local,
      TmrTaskFieldsRules.sepcon
        (tmr_task_client_clear_status_pend_argument_pre environment local critical sg call mask
          (tmr_task_timers world).(timerSignalSem) 0 perr (tmr_task_kernel world)
          eid observed tmr_task_legacy_any sg.(g_OSTmrSemSignal))
        (AppRep (tmr_task_application world)) heap).
Proof.
  intros Application AppRep environment critical sg call mask perr world eid observed
    Hprofile Hinit Hdomain Hentry heap
    [local [kernel [client [Hwhole [Hkernel
      [error [application [Hclient [Herror Happlication]]]]]]]]].
  destruct (TmrTaskFieldsRules.join_assoc application error kernel client heap
    (TmrTaskFieldsRules.join_comm _ _ _ Hclient)
    (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [owned [Hparts Hjoin]].
  assert (Hraw : TmrTaskFieldsRules.lift
    (UCOS2_C_Rules.sepcon
      (TmrTaskFields.tmr_task_fields_context environment local sg call mask (tmr_task_kernel world))
      (sem_pend_error_cell perr)) owned).
  { apply (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ owned)).
    exists kernel, error; split.
    - apply TmrTaskFieldsRules.join_comm; exact Hparts.
    - split; assumption. }
  pose proof (tmr_task_clear_status_context_split_pend_argument environment local critical sg call
    mask perr (tmr_task_kernel world) eid observed (tmr_task_client_pend_profile_enabled sg Hprofile)
    Hinit Hdomain Hentry (fst owned) Hraw) as Hargument.
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ owned) Hargument)
    as [cell [rest [Hargumentjoin [Hcell Hrest]]]].
  exists local, owned, application; split.
  - apply TmrTaskFieldsRules.join_comm; exact Hjoin.
  - split; [|exact Happlication]. exists cell, rest; split; [exact Hargumentjoin|]. split.
    + exact (proj2 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) cell Hcell).
    + intros supplied combined Hcombined Hsupplied.
      apply (proj1 (TmrTaskFieldsRules.lift_wand _ _ rest) Hrest supplied combined Hcombined).
      exact (proj1 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) supplied Hsupplied).
Qed.

(** The Sem pure carrier owns a real separated heap. Keep it as the
    residual while rebuilding the actual returned local and application
    frame. No carrier is discarded or converted to emp. *)
Lemma tmr_task_client_clear_status_pend_post_world : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical sg callback
  call mask perr signal (before : tmr_task_scan_world Application) X,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (tmr_task_client_clear_status_pend_lifted_post environment critical sg call mask signal 0 perr (fst before) X)
      (AppRep (snd before)))
    (fun heap => exists returned current local error,
      tmr_task_client_pend_program environment critical sg (tmr_task_framed_effects callback)
        call signal before (error, returned) (current, snd before) /\
      tmr_task_client_clear_status_pend_entry sg returned current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      TmrTaskFieldsRules.sepcon tmr_task_call_residual
        (tmr_task_fields_owned AppRep environment sg mask perr local returned (current, snd before)) heap).
Proof.
  intros Application AppRep environment critical sg callback call mask perr signal before X heap
    [owned [application [Hjoin [Hpost Happlication]]]].
  destruct Hpost as [returned [current [local [error Hpost]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ owned) Hpost)
    as [carrier [resources [Hsplit [Hfacts Hresources]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ resources) Hresources)
    as [error_heap [kernel [Hparts [Herror Hkernel]]]].
  destruct Hfacts as [Hprogram [Hreturn [Hsame Hentry]]].
  destruct (TmrTaskFieldsRules.join_assoc carrier resources application owned heap Hsplit Hjoin)
    as [rest [Hrest Hwhole]].
  destruct (TmrTaskFieldsRules.join_assoc kernel error_heap application resources rest
    (TmrTaskFieldsRules.join_comm _ _ _ Hparts) Hrest)
    as [client [Hclient Howner]].
  exists returned, current, local, error; split.
  - apply tmr_task_client_pend_source; assumption.
  - split; [exact Hentry|]. split; [exact Hreturn|].
    exists carrier, rest; split; [exact Hwhole|]. split; [exact I|].
    exists kernel, client; split; [exact Howner|]. split; [exact Hkernel|].
    exists error_heap, application; split; [exact Hclient|]. split; [|exact Happlication].
    assert (Hweaken : UCOS2_C_Rules.derivable1
      (UCOS2_C_Rules.store_uchar perr error) (sem_pend_error_cell perr)).
    { unfold sem_pend_error_cell; apply UCOS2_C_Rules.store_uchar_undef_store_uchar. }
    exact (Hweaken (fst error_heap) Herror).
Qed.


Lemma tmr_task_fields_entry_post_open : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical local
  sg call mask perr (before : tmr_task_scan_world Application),
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift (tmr_task_unlock_fields_entry_post
        environment critical local sg call mask (tmr_task_kernel before)
        tmr_task_fields_kernel_any))
      (tmr_task_fields_client AppRep perr before))
    (fun heap => exists returned current,
      os_sched_unlock_continuation_return_facts environment critical sg call mask
        (tmr_task_kernel before) tmr_task_fields_kernel_any returned current /\
      os_sched_unlock_fields_return_sources environment critical sg call mask
        (tmr_task_kernel before) returned current /\
      tmr_task_signal_lifetime critical sg (os_sched_call_invocation returned) current /\
      tmr_task_client_clear_status_pend_entry sg returned current /\
      tmr_task_unlock_return_branch environment critical sg call mask
        (tmr_task_kernel before) returned current /\
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsRules.lift (os_sched_unlock_fields_return_world
          environment local sg returned mask current))
        (tmr_task_fields_client AppRep perr before) heap).
Proof.
  intros Application AppRep environment critical local sg call mask perr before heap
    [owned [client [Hjoin [[returned [current [[[[Hfacts Hsources] Hlife] [Hentry Hbranch]] Hworld]]]
      Hclient]]]].
  exists returned, current; split; [exact Hfacts|].
  split; [exact Hsources|]. split; [exact Hlife|].
  split; [exact Hentry|]. split; [exact Hbranch|].
  exists owned, client; split; [exact Hjoin|]; split; assumption.
Qed.
