From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.timer Require Import tmr_task_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_task_proof_auto.
From SimpleC.CoreLang Require Import CTypes.
Import SimpleCtypeNotations.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Import TimerCallback_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_call_adapter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_witness_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_iteration_entry_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_adapter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_call_layout_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_progress_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_callback_registry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_iteration_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_vc_spec.
Import TimerCallback_C_Rules TimerCallback_C_Rules.Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.

Lemma proof_of_OSTmr_Task_entail_wit_1 : OSTmr_Task_entail_wit_1.
Proof.
  unfold OSTmr_Task_entail_wit_1; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep p_arg_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 heap Hheap.
  pose proof (tmr_task_client_outer_initial environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial X PreH15) as Houter.
  exists [], initial_context, initial; tmr_task_vc_keep_pure.
  rewrite <- PreH3; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_2 : OSTmr_Task_entail_wit_2.
Proof.
  unfold OSTmr_Task_entail_wit_2; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep context world completed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 heap Hheap.
  assert (Hprofile : sem_pend_profile sg) by (unfold tmr_task_profile in PreH1; tauto).
  assert (Hlayout : kernel_tcb_stack_field_layout sg) by (unfold tmr_task_profile in PreH1; tauto).
  destruct (tmr_task_client_status_iteration_pend_domain critical sg context
    (tmr_task_kernel world) Hprofile Hlayout PreH11) as [eid [observed [Hdomain Hentry]]].
  pose proof (proj2 (proj2 Hdomain)) as Hinput.
  exists eid, observed; tmr_task_vc_keep_pure; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_3 : OSTmr_Task_entail_wit_3.
Proof.
  unfold OSTmr_Task_entail_wit_3; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep context world completed eid observed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 heap Hheap.
  destruct Hheap as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [resources [caps [Hcapsjoin [Hresources Hcaps]]]].
  destruct (tmr_task_client_clear_status_pend_post_world Application AppRep environment critical sg callback
    context mask (&("err")) (timerSignalSem (tmr_task_timers world)) world tmr_task_legacy_any
    resources Hresources)
    as [returned [current [local [error [Hprogram [Hentry [Hsafe Hreturned_resources]]]]]]].
  pose proof Hprogram as [Hruntime [Hsame Happ]].
  pose proof (tmr_task_client_runtime_preserves_signal_lifetime environment critical sg context
    (timerSignalSem (tmr_task_timers world)) 0 (tmr_task_kernel world) error current
    PreH6 PreH7 PreH1 PreH4 Hruntime) as Hcurrent_life.
  pose proof (tmr_task_signal_lifetime_same_call critical sg context returned current
    Hsame Hcurrent_life) as Hlife.
  destruct Hreturned_resources as [carrier [owned [Hparts [Hcarrier Howned]]]].
  destruct (TmrTaskFieldsRules.join_assoc carrier owned caps resources with_caps Hparts Hcapsjoin)
    as [owner_caps [Howner_caps Hcarrier_caps]].
  destruct (TmrTaskFieldsRules.join_assoc owner_caps carrier residual with_caps heap
    (TmrTaskFieldsRules.join_comm _ _ _ Hcarrier_caps) Hwhole)
    as [combined_residual [Hresidual_join Hfinal]].
  exists local, error, returned, (current, tmr_task_application world).
  tmr_task_vc_keep_pure.
  exists owner_caps, combined_residual; split; [exact Hfinal|].
  split; [|exact I].
  exists owned, caps; split; [exact Howner_caps|]. split; assumption.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_4 : OSTmr_Task_entail_wit_4.
Proof.
  unfold OSTmr_Task_entail_wit_4; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep context world completed wait_context waited wait_local wait_error PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 heap Hheap.
  destruct Hheap as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [resources [caps [Hcapsjoin [Hresources Hcaps]]]].
  destruct (tmr_task_fields_lock_post_world Application AppRep environment critical wait_local sg
    wait_context mask (&("err")) waited resources Hresources)
    as [lock_context [locked_kernel [Hhistory [Hnormal [Hsource [Hcontrol [Hsources Howned]]]]]]].
  pose proof (tmr_task_fields_lock_source Application environment critical sg mask callback
    wait_context waited lock_context locked_kernel Hhistory) as Hlock.
  pose proof (tmr_task_client_status_lock_return_entry (task_stack_call_external environment)
    environment critical sg wait_context mask (tmr_task_kernel waited) lock_context locked_kernel
    PreH12 PreH1 PreH2 Hnormal Hsource Hcontrol Hsources) as Hentry.
  pose proof (tmr_task_lock_fields_return_preserves_signal_lifetime environment critical sg
    wait_context mask (tmr_task_kernel waited) lock_context locked_kernel PreH1 PreH4 Hsources) as Hlife.
  assert (Hwait_init : timer_api_initialized (tmr_task_timers waited)).
  { eapply tmr_task_client_pend_preserves_initialized.
    - eapply tmr_task_registered_source_clients_preserve_initialized; exact PreH12.
    - apply tmr_task_fields_bound_hook_preserves_initialized; exact PreH13.
    - exact PreH19.
    - exact PreH7. }
  pose proof (tmr_task_fields_task_lock_preserves_initialized Application environment critical sg
    mask (tmr_task_framed_effects callback) wait_context waited lock_context
    (locked_kernel, tmr_task_application waited) Hlock Hwait_init) as Hinit.
  pose proof (tmr_task_client_history_from_calls environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial context completed world wait_error
    wait_context waited lock_context (locked_kernel, tmr_task_application waited)
    (proj1 PreH18) PreH19 Hlock) as Hactual_history.
  exists {| tmr_task_continuation_before := world;
    tmr_task_continuation_context := context; tmr_task_continuation_completed := completed;
    tmr_task_continuation_error := wait_error; tmr_task_continuation_waited := waited;
    tmr_task_continuation_wait_context := wait_context;
    tmr_task_continuation_locked := (locked_kernel, tmr_task_application waited);
    tmr_task_continuation_lock_context := lock_context |}.
  tmr_task_vc_keep_pure.
  exists with_caps, residual; split; [exact Hwhole|]. split; [|exact Hresidual].
  exists resources, caps; split; [exact Hcapsjoin|]. split; assumption.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_5 : OSTmr_Task_entail_wit_5.
Proof.
  unfold OSTmr_Task_entail_wit_5; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep context world completed wait_context waited wait_error history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 heap Hheap.
  destruct Hheap as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [with_spoke [caps [Hcapsjoin [Hwith_spoke Hcaps]]]].
  destruct Hwith_spoke as [owned [spoke_heap [Hspokejoin [Howned Hspoke]]]].
  pose proof (proj1 (tmr_task_current_fields_timer_valid AppRep environment sg mask (&("err"))
    (tmr_task_continuation_lock_context history) (tmr_task_continuation_start history)
    (tmr_task_fields_profile_enabled sg PreH1) PreH4 owned Howned)) as Hvalid.
  assert (Houter : tmr_task_client_outer_facts environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial (tmr_task_continuation_context history)
    (tmr_task_continuation_completed history) (tmr_task_continuation_before history) X).
  { rewrite PreH26, PreH27, PreH28; exact PreH25. }
  pose proof (tmr_task_client_scan_initial environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history X PreH1 Houter PreH32
    Hvalid PreH4) as Hfacts.
  assert (Hsize : cfgTimerWheelSize (osKernelConfig sg) = 7)
    by (unfold tmr_task_profile, tmr_link_profile in PreH1; tauto).
  assert (Hspoke_value : unsigned_last_nbits
    (timerTime (tmr_task_timers (tmr_task_continuation_start history)) mod 7) 16 =
    Z.of_nat (tmr_task_continuation_spoke sg history)).
  { unfold tmr_task_continuation_spoke, tmr_task_spoke_index, timer_spoke.
    rewrite Hsize; unfold kernel_u16.
    pose proof (Z.mod_pos_bound
      (timerTime (tmr_task_timers (tmr_task_continuation_start history))) 7 ltac:(lia)) as Hmod.
    rewrite (Z.mod_small
      (timerTime (tmr_task_timers (tmr_task_continuation_start history)) mod 7) 65536) by lia.
    rewrite Z2Nat.id by lia.
    apply unsigned_last_nbits_eq.
    change (0 <= timerTime (tmr_task_timers (tmr_task_continuation_start history)) mod 7 < 65536).
    lia. }
  tmr_task_vc_keep_pure.
  exists with_caps, residual; split; [exact Hwhole|]. split; [|exact Hresidual].
  exists with_spoke, caps; split; [exact Hcapsjoin|]. split; [|exact Hcaps].
  exists owned, spoke_heap; split; [exact Hspokejoin|]. split; [exact Howned|].
  rewrite Z.rem_mod_nonneg in Hspoke by
    (pose proof (proj1 (proj2 (proj2 Hvalid))); lia).
  rewrite Hspoke_value in Hspoke; exact Hspoke.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_6 : OSTmr_Task_entail_wit_6.
Proof.
  unfold OSTmr_Task_entail_wit_6; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 heap Hheap.
  assert (Hvalid : valid_timer_state sg (tmr_task_timers (tmr_task_continuation_start history)))
    by (unfold tmr_task_client_scan_facts in PreH21; tauto).
  pose proof (proj2 (tmr_task_scan_at_spoke_valid sg (tmr_task_continuation_spoke sg history)
    (tmr_task_timers (tmr_task_continuation_start history)) PreH5 Hvalid)) as Hpointer.
  exists [], (tmr_task_continuation_scan sg history),
    (tmr_task_continuation_lock_context history), (tmr_task_continuation_start history).
  tmr_task_vc_keep_pure.
  change (timer_scan_next_pointer sg (tmr_task_continuation_scan sg history) =
    tmr_task_head sg (tmr_task_continuation_spoke sg history)
      (tmr_task_timers (tmr_task_continuation_start history))) in Hpointer.
  rewrite Hpointer; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_7 : OSTmr_Task_entail_wit_7.
Proof.
  unfold OSTmr_Task_entail_wit_7; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 heap Hheap.
  destruct (tmr_task_client_scan_current_image environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history visited scan_context
    scan_world cursor X PreH10 PreH1)
    as [index [tail [image [future [Hremaining [Hadvance [Hindex [Himage [Hrunning Hpointer]]]]]]]]].
  assert (Hread : tmr_task_image_read scan_world index TaskNextField
    (tmr_task_image_value TaskNextField image)) by (exists image; split; [exact Himage|reflexivity]).
  exists (tmr_task_image_value TaskNextField image), image, future, index, tail.
  tmr_task_vc_keep_pure.
  rewrite Hpointer in Hheap; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_8_1 : OSTmr_Task_entail_wit_8_1.
Proof.
  unfold OSTmr_Task_entail_wit_8_1; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future image unlinked unlinked_image linked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88 PreH89 PreH90 PreH91 PreH92 PreH93 PreH94 PreH95 heap Hheap.
  assert (Hvalid : valid_timer_state sg (tmr_task_timers scan_world))
    by (unfold tmr_task_client_scan_facts in PreH87; tauto).
  destruct (tmr_task_dispatch_prepared_from_updates Application sg scan_world unlinked linked
    index image unlinked_image cached PreH1 Hvalid PreH35 PreH53 PreH55 PreH69 PreH36
    PreH20 (or_introl (conj PreH22 PreH5))) as [dispatch_image [Hdispatch Himage]].
  assert (Hread : tmr_task_image_read scan_world index TaskMatchField
    (timerTime (tmr_task_timers scan_world))) by (exists image; split; assumption).
  exists dispatch_image, linked; tmr_task_vc_keep_pure; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_8_2 : OSTmr_Task_entail_wit_8_2.
Proof.
  unfold OSTmr_Task_entail_wit_8_2; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future image unlinked unlinked_image completed_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88 PreH89 PreH90 PreH91 PreH92 PreH93 PreH94 PreH95 PreH96 PreH97 PreH98 PreH99 heap Hheap.
  assert (Hvalid : valid_timer_state sg (tmr_task_timers scan_world))
    by (unfold tmr_task_client_scan_facts in PreH91; tauto).
  destruct (tmr_task_dispatch_prepared_from_updates Application sg scan_world unlinked completed_world
    index image unlinked_image cached PreH1 Hvalid PreH39 PreH57 PreH59 PreH73 PreH40
    PreH6 (or_intror (conj PreH26 PreH8))) as [dispatch_image [Hdispatch Himage]].
  assert (Hread : tmr_task_image_read scan_world index TaskMatchField
    (timerTime (tmr_task_timers scan_world))) by (exists image; split; assumption).
  exists dispatch_image, completed_world; tmr_task_vc_keep_pure; exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_9 : OSTmr_Task_entail_wit_9.
Proof.
  unfold OSTmr_Task_entail_wit_9; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched dispatch_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 heap Hheap.
  destruct (tmr_task_callback_domain_from_prepared Application environment critical sg mask callback
    initial_context initial history visited scan_context scan_world dispatched cursor index tail future
    cached dispatch_image X PreH24 PreH25 PreH26 PreH28 PreH29 PreH30 PreH1)
    as [Hclient_domain Hdomain].
  pose proof Hheap as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [owned [caps [Hcapsjoin [Howned Hcaps]]]].
  pose proof (proj1 (tmr_task_current_fields_timer_valid AppRep environment sg mask (&("err"))
    scan_context dispatched (tmr_task_fields_profile_enabled sg PreH2) PreH5 owned Howned)) as Hvalid.
  assert (Hready : tmr_task_fields_scan_ready sg dispatched) by (split; assumption).
  assert (Hcallback : tmr_task_image_read dispatched index TaskCallbackField
    (tmr_task_image_value TaskCallbackField dispatch_image)) by (exists dispatch_image; auto).
  assert (Hargument : tmr_task_image_read dispatched index TaskArgumentField
    (tmr_task_image_value TaskArgumentField dispatch_image)) by (exists dispatch_image; auto).
  pose proof (proj1 (tmr_task_client_status_callback_capabilities_join AppRep environment critical sg callback
    mask initial_context initial caps owned with_caps
    (TmrTaskFieldsRules.join_comm _ _ _ Hcapsjoin)) Hcaps) as Hcaps1.
  pose proof (proj1 (tmr_task_client_status_callback_capabilities_join AppRep environment critical sg callback
    mask initial_context initial with_caps residual heap Hwhole) Hcaps1) as Hcaps2.
  pose proof (tmr_task_client_status_callback_capabilities_selected AppRep environment critical sg callback
    mask initial_context initial (&("err")) (timerImageCallback dispatch_image) (timer_pool_addr sg index)
    (timerImageArg dispatch_image) scan_context dispatched Hclient_domain heap Hcaps2) as Hselected.
  exists (&("err")), (tmr_task_image_value TaskArgumentField dispatch_image); split.
  - tmr_task_vc_keep_pure; exact Hheap.
  - destruct Hselected as [Hnonnull [body [Hlookup Hevidence]]].
    split; [exact Hnonnull|]. exists body; split; [exact Hlookup|].
    intros call_context call_before.
    destruct (Hevidence call_context call_before) as [Hhoare Hcoverage].
    constructor; intros [actual_self actual_argument] frame.
    + exact (Hhoare (actual_self, actual_argument) frame).
    + exact (Hcoverage (actual_self, actual_argument) frame).
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_10 : OSTmr_Task_entail_wit_10.
Proof.
  unfold OSTmr_Task_entail_wit_10; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched dispatch_image function_pointer callback_argument callback_error_address PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 heap Hheap.
  destruct Hheap as [Hresources Hspec].
  destruct Hresources as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [owned [caps [Hcapsjoin [Hpost Hcaps]]]].
  destruct (tmr_task_client_status_callback_post_entry Application AppRep environment sg callback mask
    callback_error_address function_pointer (timer_pool_addr sg index) callback_argument scan_context
    dispatched (timer_pool_addr sg index, callback_argument) tt PreH1 owned Hpost)
    as [callback_context [callback_world [Harguments [Hfacts [Hentry Howned]]]]].
  pose proof (tmr_task_fields_callback_return_signal_lifetime Application critical sg callback
    function_pointer (timer_pool_addr sg index) callback_argument scan_context dispatched
    callback_context callback_world PreH33 PreH3 (proj1 Hfacts)) as Hlife.
  exists callback_context, callback_world; tmr_task_vc_keep_pure.
  exists with_caps, residual; split; [exact Hwhole|]. split; [|exact Hresidual].
  exists owned, caps; split; [exact Hcapsjoin|]. split; [|exact Hcaps].
  rewrite <- PreH8; exact Howned.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_11_1 : OSTmr_Task_entail_wit_11_1.
Proof.
  unfold OSTmr_Task_entail_wit_11_1; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched function_pointer callback_argument callback_context callback_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 heap Hheap.
  destruct (tmr_task_client_scan_callback_from_images environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history visited scan_context
    scan_world cursor index tail future cached dispatched function_pointer callback_argument
    callback_context callback_world X PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    PreH28 (proj1 PreH29)) as [Hstep [Hfacts Hpointer]].
  exists (index, Some (function_pointer, timer_pool_addr sg index, callback_argument)),
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers callback_world)),
    callback_context, callback_world.
  tmr_task_vc_keep_pure.
  rewrite Hpointer; revert heap Hheap; tmr_task_vc_weaken.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_11_2 : OSTmr_Task_entail_wit_11_2.
Proof.
  unfold OSTmr_Task_entail_wit_11_2; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched dispatch_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 heap Hheap.
  assert (Hnull : tmr_task_image_read dispatched index TaskCallbackField 0).
  { exists dispatch_image; split; [exact PreH30|symmetry; exact PreH1]. }
  destruct (tmr_task_client_scan_null_callback environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history visited scan_context
    scan_world cursor index tail future cached dispatched X PreH2 PreH24 PreH25 PreH26
    PreH28 PreH29 Hnull) as [Hstep [Hfacts Hpointer]].
  exists (index, None), future, scan_context, dispatched.
  tmr_task_vc_keep_pure.
  rewrite <- Hpointer; revert heap Hheap; tmr_task_vc_weaken.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_11_3 : OSTmr_Task_entail_wit_11_3.
Proof.
  unfold OSTmr_Task_entail_wit_11_3; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 heap Hheap.
  destruct (tmr_task_client_scan_not_due environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history visited scan_context
    scan_world cursor index tail future image X PreH3 PreH33 PreH34 PreH35 PreH37 PreH1)
    as [Hstep [Hfacts Hpointer]].
  exists (index, None), future, scan_context, scan_world.
  tmr_task_vc_keep_pure.
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in PreH5; tauto).
  rewrite Htime in Hheap.
  pose proof (proj2 (tmr_task_fields_pool_match_cell_view AppRep environment sg mask (&("err"))
    scan_context scan_world index image PreH3 PreH4 PreH6 PreH7 PreH8)) as Hmerge.
  assert (Hcached : cached = timer_scan_next_pointer sg future) by (rewrite PreH39; exact Hpointer).
  rewrite <- Hcached; revert heap Hheap; tmr_task_vc_weaken.
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_12 : OSTmr_Task_entail_wit_12.
Proof.
  unfold OSTmr_Task_entail_wit_12; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep history visited_2 scan_context_2 scan_world_2 cursor_2 after_context after next_cursor event PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 heap Hheap.
  exists (visited_2 ++ [event]), next_cursor, after_context, after.
  tmr_task_vc_keep_pure; revert heap Hheap; tmr_task_vc_weaken.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_7_pure : OSTmr_Task_partial_solve_wit_7_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_7_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep context world completed wait_context waited wait_error history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 heap Hheap.
  tmr_task_vc_keep_pure; reflexivity.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_8_pure : OSTmr_Task_partial_solve_wit_8_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_8_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep context world completed wait_context waited wait_error history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 heap Hheap.
  tmr_task_vc_keep_pure; exact PreH6.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_9_pure : OSTmr_Task_partial_solve_wit_9_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_9_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 heap Hheap.
  pose proof PreH9 as Hfacts; unfold tmr_task_client_scan_facts in Hfacts.
  assert (Hspoke : tmr_task_spoke_in_range sg (tmr_task_continuation_spoke sg history)) by tauto.
  assert (Hinit : timer_api_initialized (tmr_task_timers (tmr_task_continuation_start history))) by tauto.
  tmr_task_vc_keep_pure; exact Hinit.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_11_pure : OSTmr_Task_partial_solve_wit_11_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_11_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 heap Hheap.
  tmr_task_vc_keep_pure; unfold tmr_task_client_scan_facts in PreH9; tauto.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_26_pure : OSTmr_Task_partial_solve_wit_26_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_26_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched dispatch_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 heap Hheap.
  assert (Hinit : timer_api_initialized (tmr_task_timers scan_world))
    by (unfold tmr_task_client_scan_facts in PreH9; tauto).
  pose proof (tmr_task_dispatch_prepared_preserves_initialized Application sg scan_world dispatched
    index cached Hinit PreH14) as Hdispatched_init.
  tmr_task_vc_keep_pure; exact Hdispatched_init.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_29_pure : OSTmr_Task_partial_solve_wit_29_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_29_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched dispatch_image function_pointer callback_argument callback_error_address PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 heap Hheap.
  pose proof (proj2 PreH6) as Hinit.
  tmr_task_vc_keep_pure; exact Hinit.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_32_pure : OSTmr_Task_partial_solve_wit_32_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_32_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor index cached tail future dispatched function_pointer callback_argument callback_context callback_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 heap Hheap.
  assert (Hspoke : tmr_task_spoke_in_range sg (tmr_task_continuation_spoke sg history))
    by (unfold tmr_task_client_scan_facts in PreH9; tauto).
  pose proof (proj2 (proj1 (proj2 (proj1 PreH17)))) as Hinit.
  tmr_task_vc_keep_pure; exact Hinit.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_34_pure : OSTmr_Task_partial_solve_wit_34_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_34_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep history visited scan_context scan_world cursor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 heap Hheap.
  assert (Hlayout : kernel_tcb_stack_field_layout sg)
    by (unfold tmr_task_profile in PreH2; tauto).
  pose proof (tmr_task_registered_source_ready_clients
    (task_stack_call_external environment) critical PreH5) as Hready.
  assert (Hinit : timer_api_initialized (tmr_task_timers scan_world))
    by (unfold tmr_task_client_scan_facts in PreH10; tauto).
  tmr_task_vc_keep_pure; exact Hinit.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_1 : OSTmr_Task_which_implies_wit_1.
Proof.
  unfold OSTmr_Task_which_implies_wit_1; left.
  intros Application mask initial initial_context sg critical environment AppRep Hentry heap Hheap.
  pose proof (tmr_task_client_status_iteration_from_ready critical sg initial_context
    (tmr_task_kernel initial) Hentry) as Hiteration.
  split; [exact (conj Hiteration (proj1 Hiteration))|].
  exact (tmr_task_fields_base_merge_error AppRep environment sg mask
    (&("err")) initial_context initial heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_2 : OSTmr_Task_which_implies_wit_2.
Proof.
  unfold OSTmr_Task_which_implies_wit_2; left.
  intros Application mask callback sg critical environment AppRep context world eid observed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 heap Hheap.
  pose proof (proj2 (proj2 PreH10)) as Hinput.
  pose proof PreH8 as Haddresses.
  unfold tmr_task_global_addresses, os_sched_lock_global_addresses,
    os_sched_unlock_global_addresses, os_sched_global_addresses,
    sched_new_global_addresses in Haddresses.
  pose proof (tmr_task_client_pend_address_guard_from_input critical sg
    (os_sched_call_invocation context) (tmr_task_kernel world) eid observed
    (timerSignalSem (tmr_task_timers world)) (&("OSIntNesting")) (&("OSLockNesting"))
    (&("OSTCBCur")) (&("OSRdyGrp")) (&("OSRdyTbl")) Hinput PreH3
    ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto)) as Hguard.
  assert (Hsched : os_sched_global_addresses sg (&("OSIntNesting")) (&("OSLockNesting"))
    (&("OSPrioHighRdy")) (&("OSPrioCur")) (&("OSTCBHighRdy")) (&("OSTCBPrioTbl"))
    (&("OSCtxSwCtr")) (&("OSUnMapTbl")) (&("OSRdyGrp")) (&("OSRdyTbl")))
    by (unfold tmr_task_global_addresses, os_sched_unlock_global_addresses in PreH8; tauto).
  pose proof (proj1 (tmr_task_current_fields_owned_valid AppRep environment sg mask (&("err"))
    context world heap Hheap)) as Hvalid.
  destruct (tmr_task_client_clear_status_pend_argument_from_owner Application AppRep environment critical sg
    context mask (&("err")) world eid observed PreH1 PreH9 PreH10 PreH11 heap Hheap)
    as [pend_local Hargument].
  exists pend_local; tmr_task_vc_keep_pure.
  assert (Hsignal : (&("OSTmrSemSignal")) = sg.(g_OSTmrSemSignal))
    by (unfold tmr_task_global_addresses in PreH8; tauto).
  rewrite Hsignal; exact Hargument.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_3 : OSTmr_Task_which_implies_wit_3.
Proof.
  unfold OSTmr_Task_which_implies_wit_3; left.
  intros Application mask sg critical environment AppRep world wait_context waited
    wait_local Hprofile Hlife Hbindings Haddresses Hinit Hentry heap Hheap.
  pose proof (proj1 (tmr_task_global_addresses_implies_scheduler_addresses
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Haddresses)) as Hlock_addresses.
  pose proof (proj1 (tmr_task_current_fields_owned_valid AppRep environment sg mask (&("err"))
    wait_context waited heap (ex_intro _ wait_local Hheap))) as Hvalid.
  tmr_task_vc_keep_pure.
  exact (tmr_task_fields_owned_lock_pre AppRep environment sg mask (&("err"))
    critical wait_local wait_context waited heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_4 : OSTmr_Task_which_implies_wit_4.
Proof.
  unfold OSTmr_Task_which_implies_wit_4; left.
  intros Application mask sg environment AppRep history
    Hprofile Hbindings Haddresses Hinit Hentry heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in Haddresses; tauto).
  rewrite Htime.
  exact (tmr_task_fields_owned_split_time_cell AppRep environment sg mask (&("err"))
    (tmr_task_continuation_lock_context history) (tmr_task_continuation_locked history)
    Hprofile Hinit heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_5 : OSTmr_Task_which_implies_wit_5.
Proof.
  unfold OSTmr_Task_which_implies_wit_5; left.
  intros Application mask sg critical environment AppRep history
    Hentry Hprofile Hlife Hbindings Haddresses Hinit heap Hheap.
  assert (Hstart_entry : tmr_task_client_clear_status_pend_entry sg (tmr_task_continuation_lock_context history)
    (tmr_task_kernel (tmr_task_continuation_start history)))
    by (apply tmr_task_client_status_entry_replace_timers; exact Hentry).
  assert (Hstart_life : tmr_task_signal_lifetime critical sg
    (os_sched_call_invocation (tmr_task_continuation_lock_context history))
    (tmr_task_kernel (tmr_task_continuation_start history))) by exact Hlife.
  tmr_task_vc_keep_pure.
  eapply tmr_task_fields_separated_right_frame.
  - apply tmr_task_fields_time_rest_advance; assumption.
  - exact Hheap.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_6 : OSTmr_Task_which_implies_wit_6.
Proof.
  unfold OSTmr_Task_which_implies_wit_6; left.
  intros Application mask sg environment AppRep history
    Hentry Hprofile Hbindings Haddresses Hinit heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in Haddresses; tauto).
  rewrite Htime in Hheap.
  exact (tmr_task_fields_owned_merge_time_cell AppRep environment sg mask (&("err"))
    (tmr_task_continuation_lock_context history) (tmr_task_continuation_start history)
    Hprofile Hinit heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_7 : OSTmr_Task_which_implies_wit_7.
Proof.
  unfold OSTmr_Task_which_implies_wit_7; left.
  intros Application mask sg environment AppRep history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH3; tauto).
  pose proof (tmr_task_fields_wheel_head_address sg (&("OSTmrWheelTbl"))
    (tmr_task_continuation_spoke sg history) PreH1 Hwheel) as Haddress.
  change (tmr_unlink_wheel_field
    ((&("OSTmrWheelTbl")) + Z.of_nat (tmr_task_continuation_spoke sg history) *
      sizeof_alias_type "os_tmr_wheel") "OSTmrFirst" = sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat (tmr_task_continuation_spoke sg history)) in Haddress.
  unfold tmr_unlink_wheel_field in Haddress.
  cbn [Rules.sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in *.
  rewrite Haddress.
  exact (proj1 (tmr_task_fields_head_cell_view AppRep environment sg mask (&("err"))
    (tmr_task_continuation_lock_context history) (tmr_task_continuation_start history) (tmr_task_continuation_spoke sg history)
    PreH1 PreH4 PreH5) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_8 : OSTmr_Task_which_implies_wit_8.
Proof.
  unfold OSTmr_Task_which_implies_wit_8; left.
  intros Application mask sg environment AppRep history PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  pose proof (tmr_task_fields_wheel_head_address sg (&("OSTmrWheelTbl"))
    (tmr_task_continuation_spoke sg history) PreH2 Hwheel) as Haddress.
  change (tmr_unlink_wheel_field
    ((&("OSTmrWheelTbl")) + Z.of_nat (tmr_task_continuation_spoke sg history) *
      sizeof_alias_type "os_tmr_wheel") "OSTmrFirst" = sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat (tmr_task_continuation_spoke sg history)) in Haddress.
  unfold tmr_unlink_wheel_field in Haddress.
  cbn [Rules.sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in *.
  rewrite Haddress in Hheap.
  exact (proj2 (tmr_task_fields_head_cell_view AppRep environment sg mask (&("err"))
    (tmr_task_continuation_lock_context history) (tmr_task_continuation_start history) (tmr_task_continuation_spoke sg history)
    PreH2 PreH5 PreH6) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_9 : OSTmr_Task_which_implies_wit_9.
Proof.
  unfold OSTmr_Task_which_implies_wit_9; left.
  intros Application mask sg environment AppRep scan_context scan_world index cached image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 heap Hheap.
  tmr_task_vc_keep_pure.
  rewrite PreH7.
  exact (proj1 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context scan_world index image TaskNextField
    PreH1 PreH2 PreH4 PreH5 PreH6) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_10 : OSTmr_Task_which_implies_wit_10.
Proof.
  unfold OSTmr_Task_which_implies_wit_10; left.
  intros Application mask sg environment AppRep scan_context scan_world index cached image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 heap Hheap.
  tmr_task_vc_keep_pure.
  rewrite PreH8 in Hheap.
  exact (proj2 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context scan_world index image TaskNextField
    PreH2 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_11 : OSTmr_Task_which_implies_wit_11.
Proof.
  unfold OSTmr_Task_which_implies_wit_11; left.
  intros Application mask sg environment AppRep scan_context scan_world index image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in PreH3; tauto).
  rewrite Htime.
  exact (proj1 (tmr_task_fields_pool_match_cell_view AppRep environment sg mask (&("err"))
    scan_context scan_world index image PreH1 PreH2 PreH4 PreH5 PreH6) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_12 : OSTmr_Task_which_implies_wit_12.
Proof.
  unfold OSTmr_Task_which_implies_wit_12; left.
  intros Application mask sg environment AppRep scan_context scan_world index image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  rewrite Htime in Hheap.
  exact (proj2 (tmr_task_fields_pool_match_cell_view AppRep environment sg mask (&("err"))
    scan_context scan_world index image PreH2 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_13 : OSTmr_Task_which_implies_wit_13.
Proof.
  unfold OSTmr_Task_which_implies_wit_13; left.
  intros Application mask sg critical environment AppRep scan_context scan_world index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  destruct (tmr_task_fields_owned_split_unlink AppRep environment sg mask (&("err"))
    scan_context scan_world index PreH1 PreH5 PreH6 heap Hheap)
    as [unlink_local [raw_match [raw_next [previous [first [entries [unlink_frame Hparts]]]]]]].
  exists unlink_local, raw_match, raw_next, previous, first, entries, unlink_frame.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  rewrite Hwheel; exact Hparts.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_14 : OSTmr_Task_which_implies_wit_14.
Proof.
  unfold OSTmr_Task_which_implies_wit_14; left.
  intros Application mask sg critical environment AppRep scan_context scan_world index raw_match raw_next previous first entries unlink_frame unlink_local PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH5; tauto).
  rewrite Hwheel in Hheap.
  destruct (tmr_task_fields_unlink_post_merge AppRep environment sg mask (&("err"))
    unlink_local scan_context scan_world index raw_match raw_next previous first entries
    unlink_frame heap Hheap) as [unlinked [Hstep Howned]].
  destruct (tmr_task_unlink_world_initialized_eligible Application sg scan_world unlinked index
    PreH6 Hstep) as [Hinit Heligible].
  destruct (tmr_task_unlink_world_preserves_entry_lifetime Application critical sg scan_context
    scan_world unlinked index Hstep (proj1 PreH1) PreH3) as [_ Hlife].
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg scan_context
    (tmr_task_kernel unlinked)).
  { destruct Hstep as [timers [Hupdate ->]]; exact PreH1. }
  exists unlinked; tmr_task_vc_keep_pure; exact Howned.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_15 : OSTmr_Task_which_implies_wit_15.
Proof.
  unfold OSTmr_Task_which_implies_wit_15; left.
  intros Application mask sg environment AppRep scan_context index unlinked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  destruct (tmr_task_fields_eligible_image AppRep environment sg mask (&("err"))
    scan_context unlinked index PreH1 PreH4 PreH6 heap Hheap)
    as [unlinked_image [Himage Howned]].
  exists unlinked_image; tmr_task_vc_keep_pure.
  exact (proj1 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context unlinked index unlinked_image TaskOptionField
    PreH1 PreH2 PreH4 PreH5 Himage) heap Howned).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_16 : OSTmr_Task_which_implies_wit_16.
Proof.
  unfold OSTmr_Task_which_implies_wit_16; left.
  intros Application mask sg environment AppRep scan_context index unlinked unlinked_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  
  exact (proj2 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context unlinked index unlinked_image TaskOptionField
    PreH2 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_17 : OSTmr_Task_which_implies_wit_17.
Proof.
  unfold OSTmr_Task_which_implies_wit_17; left.
  intros Application mask sg critical environment AppRep scan_context index unlinked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  destruct (tmr_task_fields_owned_split_link AppRep environment sg mask (&("err"))
    scan_context unlinked index PreH1 PreH5 PreH6 heap Hheap)
    as [link_local [delay [period [link_first [link_entries [link_frame Hparts]]]]]].
  exists link_local, delay, period, link_first, link_entries, link_frame.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  rewrite Hwheel, Htime; exact Hparts.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_18 : OSTmr_Task_which_implies_wit_18.
Proof.
  unfold OSTmr_Task_which_implies_wit_18; left.
  intros Application mask sg critical environment AppRep scan_context index unlinked delay period link_first link_entries link_frame link_local PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 heap Hheap.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH5; tauto).
  assert (Htime : (&("OSTmrTime")) = sg.(g_OSTmrTime))
    by (unfold tmr_task_global_addresses in PreH5; tauto).
  rewrite Hwheel, Htime in Hheap.
  destruct (tmr_task_fields_link_post_merge AppRep environment sg mask (&("err"))
    link_local scan_context unlinked index delay period link_first link_entries
    link_frame heap Hheap) as [linked [Hstep Howned]].
  destruct (tmr_task_link_world_preserves_entry_lifetime Application critical sg scan_context
    unlinked linked index Hstep (proj1 PreH1) PreH3) as [_ Hlife].
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg scan_context
    (tmr_task_kernel linked)).
  { destruct Hstep as [timers [Hupdate ->]]; exact PreH1. }
  exists linked; tmr_task_vc_keep_pure; exact Howned.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_19 : OSTmr_Task_which_implies_wit_19.
Proof.
  unfold OSTmr_Task_which_implies_wit_19; left.
  intros Application mask sg environment AppRep scan_context index unlinked unlinked_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  
  exact (proj2 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context unlinked index unlinked_image TaskOptionField
    PreH2 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_20 : OSTmr_Task_which_implies_wit_20.
Proof.
  unfold OSTmr_Task_which_implies_wit_20; left.
  intros Application mask sg environment AppRep scan_context index unlinked unlinked_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 heap Hheap.
  tmr_task_vc_keep_pure.
  exact (tmr_task_fields_owned_split_completed_state_cell AppRep environment sg mask (&("err"))
    scan_context unlinked index unlinked_image PreH1 PreH2 PreH4 PreH5 PreH6 heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_21 : OSTmr_Task_which_implies_wit_21.
Proof.
  unfold OSTmr_Task_which_implies_wit_21; left.
  intros Application mask sg critical environment AppRep scan_context index unlinked unlinked_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 heap Hheap.
  destruct (tmr_task_fields_completed_state_cell_merge AppRep environment sg mask (&("err"))
    scan_context unlinked index unlinked_image PreH2 PreH4 PreH6 PreH7 PreH8 PreH9 heap Hheap)
    as [completed_world [Hstep Howned]].
  destruct (tmr_task_complete_world_preserves_entry_lifetime Application critical sg scan_context
    unlinked completed_world index Hstep (proj1 PreH1) PreH3) as [_ Hlife].
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg scan_context
    (tmr_task_kernel completed_world)).
  { destruct Hstep as [timers [Hupdate ->]]; exact PreH1. }
  exists completed_world; tmr_task_vc_keep_pure; exact Howned.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_22 : OSTmr_Task_which_implies_wit_22.
Proof.
  unfold OSTmr_Task_which_implies_wit_22; left.
  intros Application mask sg environment AppRep scan_context index dispatched dispatch_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  
  exact (proj1 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context dispatched index dispatch_image TaskCallbackField
    PreH1 PreH2 PreH4 PreH5 PreH6) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_23 : OSTmr_Task_which_implies_wit_23.
Proof.
  unfold OSTmr_Task_which_implies_wit_23; left.
  intros Application mask sg environment AppRep scan_context index dispatched dispatch_image PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 heap Hheap.
  tmr_task_vc_keep_pure.
  
  exact (proj2 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context dispatched index dispatch_image TaskCallbackField
    PreH2 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_24 : OSTmr_Task_which_implies_wit_24.
Proof.
  unfold OSTmr_Task_which_implies_wit_24; left.
  intros Application mask callback sg environment AppRep index function_pointer callback_argument callback_error_address heap Hheap.
  destruct Hheap as [Hbase Hcapability]; split; [exact Hbase|].
  eapply TmrTaskFieldsCallback.func_ptr_spec_mono; [|exact Hcapability].
  intros body owned Hbody call_context call_before.
  eapply TmrTaskFieldsCallback.HoareFun_conseq with
    (P := fun '(self, argument) => tmr_task_client_status_callback_pre AppRep environment sg mask
      callback_error_address function_pointer (timer_pool_addr sg index)
      callback_argument call_context call_before (self, argument))
    (Q := fun '(self, argument) (_ : unit) => tmr_task_client_status_callback_post AppRep environment sg
      callback mask callback_error_address function_pointer (timer_pool_addr sg index)
      callback_argument call_context call_before (self, argument) tt).
  - intros [self argument].
    apply tmr_task_fields_callback_argument_pre_closed.
  - intros [self argument] [] state Hpost; exact Hpost.
  - exact (Hbody call_context call_before).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_25 : OSTmr_Task_which_implies_wit_25.
Proof.
  unfold OSTmr_Task_which_implies_wit_25; left.
  intros Application mask sg critical environment AppRep scan_context index dispatched dispatch_image callback_argument PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 heap Hheap.
  tmr_task_vc_keep_pure.
  rewrite PreH8.
  exact (proj1 (tmr_task_fields_pool_image_cell_view AppRep environment sg mask (&("err"))
    scan_context dispatched index dispatch_image TaskArgumentField
    PreH1 PreH3 PreH5 PreH6 PreH7) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_26 : OSTmr_Task_which_implies_wit_26.
Proof.
  unfold OSTmr_Task_which_implies_wit_26; left.
  intros Application mask sg critical environment AppRep scan_context index dispatched dispatch_image function_pointer callback_argument callback_error_address PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 heap Hheap.
  tmr_task_vc_keep_pure.
  rewrite PreH8.
  eapply (tmr_task_fields_callback_argument_rest_from_image AppRep environment sg
    mask (&("err")) function_pointer index callback_argument scan_context dispatched dispatch_image);
    try eassumption.
  - unfold tmr_task_profile in PreH2; tauto.
  - apply tmr_task_fields_profile_enabled; exact PreH2.
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_27 : OSTmr_Task_which_implies_wit_27.
Proof.
  unfold OSTmr_Task_which_implies_wit_27; left.
  intros Application mask sg environment AppRep history callback_context callback_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH3; tauto).
  pose proof (tmr_task_fields_wheel_head_address sg (&("OSTmrWheelTbl"))
    (tmr_task_continuation_spoke sg history) PreH1 Hwheel) as Haddress.
  change (tmr_unlink_wheel_field
    ((&("OSTmrWheelTbl")) + Z.of_nat (tmr_task_continuation_spoke sg history) *
      sizeof_alias_type "os_tmr_wheel") "OSTmrFirst" = sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat (tmr_task_continuation_spoke sg history)) in Haddress.
  unfold tmr_unlink_wheel_field in Haddress.
  cbn [Rules.sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in *.
  rewrite Haddress.
  exact (proj1 (tmr_task_fields_head_cell_view AppRep environment sg mask (&("err"))
    callback_context callback_world (tmr_task_continuation_spoke sg history)
    PreH1 PreH4 PreH5) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_28 : OSTmr_Task_which_implies_wit_28.
Proof.
  unfold OSTmr_Task_which_implies_wit_28; left.
  intros Application mask sg environment AppRep history callback_context callback_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 heap Hheap.
  tmr_task_vc_keep_pure.
  assert (Hwheel : (&("OSTmrWheelTbl")) = sg.(g_OSTmrWheelTbl))
    by (unfold tmr_task_global_addresses in PreH4; tauto).
  pose proof (tmr_task_fields_wheel_head_address sg (&("OSTmrWheelTbl"))
    (tmr_task_continuation_spoke sg history) PreH2 Hwheel) as Haddress.
  change (tmr_unlink_wheel_field
    ((&("OSTmrWheelTbl")) + Z.of_nat (tmr_task_continuation_spoke sg history) *
      sizeof_alias_type "os_tmr_wheel") "OSTmrFirst" = sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat (tmr_task_continuation_spoke sg history)) in Haddress.
  unfold tmr_unlink_wheel_field in Haddress.
  cbn [Rules.sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in *.
  rewrite Haddress in Hheap.
  exact (proj2 (tmr_task_fields_head_cell_view AppRep environment sg mask (&("err"))
    callback_context callback_world (tmr_task_continuation_spoke sg history)
    PreH2 PreH5 PreH6) heap Hheap).
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_29 : OSTmr_Task_which_implies_wit_29.
Proof.
  unfold OSTmr_Task_which_implies_wit_29; left.
  intros Application mask callback sg critical environment AppRep scan_context scan_world PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 heap Hheap.
  pose proof (proj1 (proj2 (tmr_task_global_addresses_implies_scheduler_addresses
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PreH8))) as Hunlock_addresses.
  pose proof (tmr_task_registered_source_unlock_clients
    (task_stack_call_external environment) critical scan_context PreH4) as Hclients.
  pose proof (proj1 (tmr_task_current_fields_owned_valid AppRep environment sg mask (&("err"))
    scan_context scan_world heap Hheap)) as Hvalid.
  destruct (tmr_task_current_fields_unlock_pre AppRep environment sg mask (&("err"))
    critical scan_context scan_world PreH10 PreH11 heap Hheap)
    as [unlock_local [owned [client [Hjoin [Hpre Hclient]]]]].
  exists unlock_local; tmr_task_vc_keep_pure.
  exists owned, client; split; [exact Hjoin|]. split; [|exact Hclient].
  split; [exact (conj (proj1 PreH12) Hclients)|exact Hpre].
Qed.

Lemma proof_of_OSTmr_Task_which_implies_wit_30 : OSTmr_Task_which_implies_wit_30.
Proof.
  unfold OSTmr_Task_which_implies_wit_30; left.
  intros Application mask sg critical environment AppRep scan_context scan_world unlock_local heap Hheap.
  destruct (tmr_task_fields_entry_post_open Application AppRep environment critical unlock_local
    sg scan_context mask (&("err")) scan_world heap Hheap)
    as [returned [current [Hfacts [Hsources [Hlife [Hentry [Hbranch Howned]]]]]]].
  exists returned, current; tmr_task_vc_keep_pure; exact Howned.
Qed.

Lemma proof_of_OSTmr_Task_partial_solve_wit_35_pure : OSTmr_Task_partial_solve_wit_35_pure.
Proof.
  unfold OSTmr_Task_partial_solve_wit_35_pure; left.
  intros Application X argument mask initial initial_context callback sg critical environment AppRep
    history visited scan_context scan_world cursor unlock_local
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    PreH24 PreH25 heap Hheap.
  tmr_task_vc_keep_pure; exact (proj2 PreH2).
Qed.

Lemma proof_of_OSTmr_Task_entail_wit_13 : OSTmr_Task_entail_wit_13.
Proof.
  unfold OSTmr_Task_entail_wit_13; left.
  intros Application X mask initial initial_context callback sg critical environment AppRep
    history visited scan_context scan_world cursor unlock_local returned unlock_kernel
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 heap Hheap.
  pose proof (tmr_task_fields_unlock_source Application environment critical sg mask callback
    scan_context scan_world returned unlock_kernel (proj1 PreH1)) as Hunlock.
  destruct (tmr_task_client_scan_exit environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial history visited scan_context
    scan_world cursor returned (unlock_kernel, tmr_task_application scan_world) X
    PreH8 PreH29 PreH20 Hunlock) as [Hiteration Houter].
  pose proof (tmr_task_client_status_iteration_from_lifetime critical sg returned
    unlock_kernel
    (EventStateDef.Build_OSEventAbstractState EventStateDef.OS_EVENT_TYPE_SEM
      None None None None nil 0%nat 0 None None None None) PreH4 PreH3) as Hentry.
  assert (Hinit : timer_api_initialized (tmr_task_timers
    (unlock_kernel, tmr_task_application scan_world))).
  { eapply tmr_task_fields_unlock_program_preserves_initialized.
    - eapply tmr_task_registered_source_clients_preserve_initialized; exact PreH11.
    - exact (proj1 Hunlock).
    - exact PreH16. }
  destruct Hheap as [with_caps [residual [Hwhole [Hwith_caps Hresidual]]]].
  destruct Hwith_caps as [with_spoke [caps [Hcapsjoin [Hwith_spoke Hcaps]]]].
  destruct Hwith_spoke as [with_pspoke [spoke [Hspokejoin [Hwith_pspoke Hspoke]]]].
  destruct Hwith_pspoke as [with_ptmr [pspoke [Hpspokejoin [Hwith_ptmr Hpspoke]]]].
  destruct Hwith_ptmr as [resources [ptmr [Hptmrjoin [Hresources Hptmr]]]].
  destruct Hresources as [kernel [client [Hresourcejoin [Hworld Hclient]]]].
  assert (Howned : tmr_task_current_fields_owned AppRep environment sg mask (&("err"))
    returned (unlock_kernel, tmr_task_application scan_world) resources).
  { destruct Hworld as [Hclosed|[reference [next_local [Hfresh Hclosed]]]].
    - exists unlock_local, kernel, client; split; [exact Hresourcejoin|].
      split; assumption.
    - exists next_local, kernel, client; split; [exact Hresourcejoin|].
      split; assumption. }
  pose proof (proj1 (tmr_task_current_fields_timer_valid AppRep environment sg mask (&("err"))
    returned (unlock_kernel, tmr_task_application scan_world)
    (tmr_task_fields_profile_enabled sg PreH8) Hinit resources Howned)) as Hvalid.
  exists (tmr_task_continuation_completed history ++
    [{| tmr_task_wait_error := tmr_task_continuation_error history;
        tmr_task_iteration_events := visited; tmr_task_iteration_context := returned |}]),
    (unlock_kernel, tmr_task_application scan_world).
  tmr_task_vc_keep_pure.
  exists with_caps, residual; split; [exact Hwhole|]. split; [|exact Hresidual].
  exists with_spoke, caps; split; [exact Hcapsjoin|]. split; [|exact Hcaps].
  exists with_pspoke, spoke; split; [exact Hspokejoin|]. split.
  - exists with_ptmr, pspoke; split; [exact Hpspokejoin|]. split.
    + exists resources, ptmr; split; [exact Hptmrjoin|]. split; [exact Howned|].
      eapply tmr_task_fields_store_ptr_forget; exact Hptmr.
    + eapply tmr_task_fields_store_ptr_forget; exact Hpspoke.
  - eapply tmr_task_fields_store_ushort_forget; exact Hspoke.
Qed.
