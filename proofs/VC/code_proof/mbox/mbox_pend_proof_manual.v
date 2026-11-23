Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.mbox Require Import mbox_pend_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_pend_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_pend_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxPend_entail_wit_1 : OSMboxPend_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range &((pe) # "os_event" ->ₛ "OSEventType")
    (event_slot_type_value before.(EventState) eid)); Intros.
  prop_apply_p (store_uint_range (&("timeout")) timeout_pre); Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_entail_wit_2 : OSMboxPend_entail_wit_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)); Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_entail_wit_3 : OSMboxPend_entail_wit_3.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("OSLockNesting")) before.(IntrState).(lockNesting)); Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_entail_wit_4 : OSMboxPend_entail_wit_4.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range &(((task_slot_addr (sg) (tid))) # "os_tcb" ->ₛ "OSTCBStat")
    (encode_task_status old.(stat))); Intros.
  prop_apply_p (store_uint_range &(((task_slot_addr (sg) (tid))) # "os_tcb" ->ₛ "OSTCBDly") old.(dly)); Intros.
  prop_apply_p (store_uint_range (&("cpu_sr")) retval); Intros.
  prop_apply_p (store_uint_range (&("timeout")) ticks); Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_entail_wit_5_1 : OSMboxPend_entail_wit_5_1.
Proof.
  right; intros; entailer!.
  eapply q_pend_resume_cleanup_ok; [exact PreH3|symmetry; exact PreH68|reflexivity].
Qed.

Lemma proof_of_OSMboxPend_entail_wit_5_2 : OSMboxPend_entail_wit_5_2.
Proof.
  right; intros; entailer!.
  eapply q_pend_resume_cleanup_abort; [exact PreH3|symmetry; eassumption].
Qed.

Lemma proof_of_OSMboxPend_return_wit_1 : OSMboxPend_return_wit_1.
Proof.
  left; intros.
  destruct PreH1 as [error [Hcode Hcleanup]].
  unfold mbox_pend_restore_output; Intros returned current.
  assert (Hreturn : q_pend_call_history external environment critical sg resumed checkpoint returned current)
    by tauto.
  assert (Hprogram : mbox_pend_api_program external environment critical sg context pe eid ticks mask
    before (error, pmsg) current).
  { eapply mbox_pend_resume_checkpoint_return; eassumption. }
  pose proof (mbox_pend_api_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram PreH2) as Hsafe.
  assert (Hsame : kernel_stack_call_history_spec.kernel_stack_call_same_call returned context).
  { destruct PreH4 as [scheduled [selected [[entered [waiting [released [unmasked
      [[[entry [Hfirst Hwait]] Hrelease] Hschedule]]]]] Hresume]]].
    pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hfirst) as Hsame_first.
    pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hrelease) as Hsame_release.
    pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hresume) as Hsame_resume.
    pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hreturn) as Hsame_return.
    destruct environment as [owned|]; [|contradiction].
    destruct Hschedule as [sched_entered [acquired [sched_resumed [sched_released
      [Hsave [Hbody Hrestore]]]]]].
    pose proof (proj1 (proj2 Hsave)) as Hsame_save.
    pose proof (task_resume_spec.os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hsame_body.
    pose proof (proj1 (proj2 Hrestore)) as Hsame_restore.
    unfold kernel_stack_call_history_spec.kernel_stack_call_same_call,
      task_tcb_init_stack_interface_spec.task_tcb_init_stack_same_call in *.
    intuition congruence. }
  unfold mbox_pend_api_post; Exists returned current error.
  rewrite Hcode; entailer!.
Qed.

Lemma proof_of_OSMboxPend_return_wit_2 : OSMboxPend_return_wit_2.
Proof.
  left; intros.
  unfold mbox_pend_restore_output; Intros returned current.
  assert (Hhistory : q_pend_call_history external environment critical sg entered checkpoint returned current) by tauto.
  pose proof (mbox_pend_immediate_checkpoint_return external environment critical sg context pe eid ticks mask
    before entered entry (mbox_message_ptr mailbox) checkpoint returned current PreH4 PreH1 Hhistory) as Hprogram.
  pose proof (mbox_pend_api_safe_return external environment critical sg context pe eid ticks mask before
    (mbox_message_ptr mailbox) OS_ERR_NONE current X Hprogram PreH37) as Hsafe.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hsame_return.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ (proj1 PreH1)) as Hsame_enter.
  assert (Hsame : Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.kernel_stack_call_same_call returned context).
  { unfold Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.kernel_stack_call_same_call in *; intuition congruence. }
  unfold mbox_pend_api_post; Exists returned current OS_ERR_NONE.
  subst perr_pre; cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSMboxPend_return_wit_3 : OSMboxPend_return_wit_3.
Proof.
  left; intros.
  assert (Hintzero : before.(IntrState).(intNesting) = 0) by lia.
  assert (Hprogram : mbox_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEND_LOCKED, 0) before).
  { apply mbox_pend_api_early_return; rewrite PreH10, Hintzero.
    apply mbox_pend_precritical_locked; lia. }
  pose proof (mbox_pend_api_safe_return external environment critical sg context pe eid ticks mask
    before 0 OS_ERR_PEND_LOCKED before X Hprogram PreH33) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context)
    by (unfold kernel_stack_call_same_call; auto).
  pose proof PreH7 as [Hint [Hlock _]].
  pose proof (sem_pend_interrupt_merge sg before PreH9) as Hmerge.
  rewrite <- Hint, <- Hlock in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold mbox_pend_api_post; Exists context before OS_ERR_PEND_LOCKED.
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  subst perr_pre; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_return_wit_4 : OSMboxPend_return_wit_4.
Proof.
  left; intros.
  assert (Hprogram : mbox_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEND_ISR, 0) before).
  { apply mbox_pend_api_early_return; rewrite PreH7; apply mbox_pend_precritical_isr; lia. }
  pose proof (mbox_pend_api_safe_return external environment critical sg context pe eid ticks mask
    before 0 OS_ERR_PEND_ISR before X Hprogram PreH30) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context)
    by (unfold kernel_stack_call_same_call; auto).
  pose proof PreH4 as [Hint [Hlock _]].
  pose proof (sem_pend_interrupt_merge sg before PreH6) as Hmerge.
  rewrite <- Hint, <- Hlock in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold mbox_pend_api_post; Exists context before OS_ERR_PEND_ISR.
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  subst perr_pre; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_return_wit_5 : OSMboxPend_return_wit_5.
Proof.
  left; intros.
  assert (Hprogram : mbox_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_EVENT_TYPE, 0) before).
  { apply mbox_pend_api_early_return; apply mbox_pend_precritical_type; assumption. }
  pose proof (mbox_pend_api_safe_return external environment critical sg context pe eid ticks mask
    before 0 OS_ERR_EVENT_TYPE before X Hprogram PreH24) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context)
    by (unfold kernel_stack_call_same_call; auto).
  pose proof PreH8 as [Htype _].
  rewrite Htype at 1.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH13).
  unfold mbox_pend_api_post; Exists context before OS_ERR_EVENT_TYPE.
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  subst perr_pre; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_return_wit_6 : OSMboxPend_return_wit_6.
Proof.
  left; intros.
  assert (Hprogram : mbox_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEVENT_NULL, 0) before).
  { apply mbox_pend_api_early_return; rewrite PreH12; apply mbox_pend_precritical_null. }
  pose proof (mbox_pend_api_safe_return external environment critical sg context pe eid ticks mask
    before 0 OS_ERR_PEVENT_NULL before X Hprogram PreH11) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context)
    by (unfold kernel_stack_call_same_call; auto).
  unfold mbox_pend_api_post; Exists context before OS_ERR_PEVENT_NULL.
  subst perr_pre; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_partial_solve_wit_10_pure : OSMboxPend_partial_solve_wit_10_pure.
Proof.
  left; intros.
  unfold Ucos2Verify.VC.code.sched.spec.sched_spec.os_sched_global_addresses,
    Ucos2Verify.VC.code.sched.spec.sched_new_spec.sched_new_global_addresses in *; entailer!; tauto.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_1 : OSMboxPend_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH1 as Hinput.
  destruct Hinput as [Hnull | [Hnon [Haddress [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  pose proof PreH3 as [Htype _].
  unfold sem_pend_continuation_save_input.
  rewrite mutex_query_closed_equiv.
  pose proof (sem_query_type_split_full sg before eid observed Hslot) as Hsplit.
  rewrite <- Htype in Hsplit.
  sep_apply_l_atomic Hsplit.
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_2 : OSMboxPend_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH3 as [Htype _].
  pose proof PreH2 as [Hint [Hlock _]].
  pose proof (sem_query_type_merge_full sg before eid PreH1) as Hmerge.
  rewrite <- Htype in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (sem_pend_interrupt_split sg before) as Hsplit.
  rewrite <- Hint, <- Hlock in Hsplit.
  sep_apply_l_atomic Hsplit.
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_3 : OSMboxPend_which_implies_wit_3.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)); Intros.
  prop_apply_p (store_uchar_range (&("OSLockNesting")) before.(IntrState).(lockNesting)); Intros.
  assert (Hintzero : before.(IntrState).(intNesting) = 0) by lia.
  assert (Hlockzero : before.(IntrState).(lockNesting) = 0) by lia.
  assert (Hprefix : mbox_pend_api_prefix pe before eid).
  { unfold mbox_pend_api_prefix; split; [|auto].
    rewrite PreH5, Hintzero, Hlockzero; apply mbox_pend_precritical_clear; assumption. }
  pose proof PreH8 as [Hint [Hlock _]].
  pose proof (sem_pend_interrupt_merge sg before PreH1) as Hmerge.
  rewrite <- Hint, <- Hlock in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold mbox_pend_save_input, mbox_pend_save_phase_pre,
    sem_pend_continuation_save_input.
  rewrite mutex_query_closed_equiv.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_4 : OSMboxPend_which_implies_wit_4.
Proof.
  left; intros.
  destruct PreH1 as [_ [_ [_ [_ [_ Hptr]]]]].
  rewrite (mbox_pend_save_output_split_message external platform environment critical saved_local
    sg context pe eid observed mask cpu_sr before).
  Intros entered entry current mailbox.
  Exists entered entry current mailbox.
  rewrite Hptr, PreH4; entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_5 : OSMboxPend_which_implies_wit_5.
Proof.
  left; intros.
  destruct PreH4 as [_ [_ [_ [_ [_ Hptr]]]]].
  rewrite Hptr, PreH3.
  rewrite (mbox_pend_message_take_checkpoint external platform environment critical saved_local
    sg context entered_2 mask cpu_sr pe before entry_2 eid observed current mailbox ticks ltac:(congruence)).
  Intros.
  Exists entered_2 entry_2 (mbox_accept_update entry_2 eid current mailbox).
  subst pmsg; entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_6 : OSMboxPend_which_implies_wit_6.
Proof.
  left; intros.
  destruct PreH4 as [_ [_ [_ [_ [_ Hptr]]]]].
  rewrite Hptr, PreH3.
  rewrite (mbox_pend_message_merge external platform environment critical saved_local
    sg context entered_2 mask cpu_sr pe before entry_2 eid observed current_2 mailbox).
  Intros.
  assert (Hphase : mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg context entered_2 mask cpu_sr before entry_2) by tauto.
  assert (Hfacts : mbox_pend_acquire_facts critical sg (os_sched_call_invocation context)
    eid mask cpu_sr before entry_2 observed current_2) by tauto.
  assert (Hfields : mboxFields current_2 = Some mailbox) by tauto.
  pose proof Hfacts as [Hinterval [Hvalid [Hsaved [Hobserved [Hlookup [Htype0 [Htype Hgen]]]]]]].
  pose proof Hphase as [Hhistory [Hsaved0 [actual [Hfacts0 Hempty]]]].
  assert (actual = current_2) as ->.
  { destruct Hfacts0 as [_ [_ [_ [_ [Hlookup0 _]]]]]; unfold mutex_query_lookup in *; congruence. }
  destruct (Hempty mailbox Hfields ltac:(congruence)) as [[owned [Howned Hclients]] [Htask Hblocking]].
  pose proof Htask as [Hsource [Hrunning [old [Hready [Hgeneration [Hnonidle [Hnone [Hmulti Hflag]]]]]]]].
  pose proof (Ucos2Verify.lib.sched.sched_current_ready_at_implies_current_consistency _ _ _ _ Hready) as Hcache.
  destruct Hready as [Hold [Hcurrent [Hpriority [Hin Hready]]]].
  pose proof (mbox_pend_empty_message sg entry_2 eid current_2 mailbox Hvalid Hlookup Htype Hfields
    ltac:(congruence)) as Hempty_message.
  assert (Hentry : mbox_pend_wait_entry sg entry_2 eid current_2
    (stackLeaseSlot (os_sched_call_stack entered_2)) old).
  { unfold mbox_pend_wait_entry; repeat first [assumption | split]; exists mailbox; auto. }
  assert (Hsnapshot : mbox_pend_empty_snapshot external environment critical sg context entered_2
    mask cpu_sr pe before entry_2 eid observed current_2 (stackLeaseSlot (os_sched_call_stack entered_2)) old).
  { unfold mbox_pend_empty_snapshot; repeat first [assumption | split]; eauto. }
  pose proof (q_pend_wait_prefix_split sg entry_2 (stackLeaseSlot (os_sched_call_stack entered_2)) old
    Hvalid Hcurrent Hold) as Hsplit.
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold mbox_pend_masked_frame, q_pend_masked_frame, sem_pend_optional_continuation_resources.
  rewrite Howned; Intros.
  Exists entered_2 entry_2 current_2 (stackLeaseSlot (os_sched_call_stack entered_2)) old owned.
  unfold mbox_pend_masked_frame, q_pend_masked_frame, sem_pend_optional_continuation_resources.
  rewrite PreH6; entailer!.
  rewrite <- Howned; exact Hsnapshot.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_7 : OSMboxPend_which_implies_wit_7.
Proof.
  left; intros.
  pose proof (proj1 (proj2 PreH1)) as Hentry.
  pose proof (mbox_pend_wait_prefix_split_call sg entry eid current tid old ticks Hentry) as Hsplit.
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address] in Hsplit.
  rewrite PreH2, Hsplit; entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_8 : OSMboxPend_which_implies_wit_8.
Proof.
  left; intros.
  pose proof (proj1 (proj2 PreH1)) as Hentry.
  destruct (mbox_pend_empty_wait_phase external environment critical sg context entered mask cpu_sr
    pe before entry eid observed current tid old ticks PreH1 PreH2) as [Hcheckpoint Hphase].
  pose proof (proj1 PreH1) as [_ [Hsaved _]].
  assert (Howned : exists owned, environment = Some owned /\ mbox_sched_clients owned critical).
  { destruct PreH1 as [_ [_ [_ [_ [_ Howned]]]]]; exact Howned. }
  Exists (event_pend_state sg entry eid current tid old PendMbox ticks).
  unfold mbox_pend_masked_frame, q_pend_masked_frame.
  sep_apply_l_atomic (mbox_pend_wait_call_continuations_merge external platform environment saved_local
    sg entered entry eid current tid old ticks Hentry).
  unfold mbox_pend_restore_input, mbox_pend_masked_frame, q_pend_masked_frame; entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_9 : OSMboxPend_which_implies_wit_9.
Proof.
  left; intros.
  unfold mbox_pend_restore_output; Intros released unmasked.
  assert (Hhistory : q_pend_call_history external environment critical sg entered waiting released unmasked) by tauto.
  assert (Howned : exists owned, environment = Some owned /\ mbox_sched_clients owned critical) by tauto.
  assert (Hphase : mbox_sched_restore_phase_pre (MboxPendWaitPhase context mask eid)
    environment critical sg released mask unmasked) by tauto.
  destruct Howned as [owned [Howned Hclients]]; subst environment.
  assert (Hidentities : sem_pend_continuation_save_input external platform (Some owned) critical saved_local
    sg released mask unmasked |--
    coq_prop (external = task_stack_call_external owned /\ platform = task_stack_call_platform owned) &&
    sem_pend_continuation_save_input external platform (Some owned) critical saved_local sg released mask unmasked).
  { unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources; entailer!. }
  sep_apply_l_atomic Hidentities; Intros.
  assert (Hexternal : external = task_stack_call_external owned) by tauto.
  assert (Hplatform : platform = task_stack_call_platform owned) by tauto.
  subst external platform.
  assert (Hcheckpoint : mbox_pend_scheduling_checkpoint (task_stack_call_external owned) (Some owned)
    critical sg context before eid ticks released unmasked).
  { exists entered, waiting; split; assumption. }
  Exists released unmasked owned.
  unfold mbox_sched_continuation_phase_sched_input, sem_pend_continuation_sched_input.
  rewrite sem_pend_continuation_save_input_owned.
  rewrite task_tcb_init_continuation_save_input_closed_world.
  unfold Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.os_sched_continuation_pre, mbox_pend_sched_admitted; entailer!; eauto.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_10 : OSMboxPend_which_implies_wit_10.
Proof.
  left; intros; subst environment external platform.
  unfold mbox_sched_continuation_phase_sched_output; Intros scheduled selected.
  assert (Hcheckpoint : mbox_pend_scheduled_checkpoint (task_stack_call_external owned)
    (Some owned) critical sg context before eid ticks scheduled selected).
  { destruct PreH4 as [entered [waiting Hreleased]].
    exists entered, waiting, released, unmasked; tauto. }
  Exists scheduled selected.
  unfold mbox_pend_save_input, mbox_pend_save_phase_pre.
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_11 : OSMboxPend_which_implies_wit_11.
Proof.
  left; intros.
  unfold mbox_pend_save_output; Intros resumed resume_entry.
  match goal with H : mbox_pend_save_phase_observation _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hhistory [Hsaved [Howned [Hselected [node Hentry]]]]]
  end.
  pose proof Hentry as [Hvalid [Hcur [Hnode _]]].
  pose proof (q_pend_cleanup_split sg resume_entry
    (task_stack.stackLeaseSlot (os_sched_call_stack context)) node Hvalid Hcur Hnode) as Hsplit.
  cbn [task_storage.tcb_cell task_storage.tcb_field_address] in Hsplit.
  rewrite <- PreH2 in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists (task_stack.stackLeaseSlot (os_sched_call_stack context)) node resumed resume_entry.
  entailer!.
  exists scheduled, selected; split; assumption.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_12 : OSMboxPend_which_implies_wit_12.
Proof.
  left; intros.
  pose proof PreH1 as [Hvalid [_ [Hnode _]]].
  pose proof Hvalid as [_ [Htasks _]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority resume_tid node Hnode).
  unfold stable_glob_vars.task_priority_in_range in Hpriority.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (q_pend_remove_call_cleanup_split external platform environment saved_local sg resumed
    resume_entry eid current resume_tid node PreH1 PreH2 PreH3 PreH4) as Hsplit.
  cbn [task_storage.tcb_cell task_storage.tcb_field_address] in Hsplit.
  rewrite <- PreH5 in Hsplit.
  unfold mbox_pend_masked_frame, q_pend_masked_frame.
  sep_apply_l_atomic Hsplit; Intros.
  Exists (event_task_remove_state resume_entry eid current resume_tid node) (task.task_set_event_ptr node None).
  cbn [task.task_set_event_ptr stat statPend eventPtr msg encode_event_link].
  entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_13 : OSMboxPend_which_implies_wit_13.
Proof.
  left; intros.
  pose proof PreH1 as [Hvalid [_ [Hnode _]]].
  pose proof Hvalid as [_ [Htasks _]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority resume_tid node Hnode).
  unfold stable_glob_vars.task_priority_in_range in Hpriority.
  rewrite Z.quot_div_nonneg by lia.
  destruct (q_pend_resume_timeout_lookup sg resume_entry eid resume_tid node PreH1 PreH2 PreH3)
    as [Htimeout [current [Hlookup Hin]]].
  pose proof (q_pend_resume_split_remove_call sg resume_entry eid resume_tid node current
    PreH1 Hlookup PreH4) as Hsplit.
  cbn [task_storage.tcb_cell task_storage.tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists current; entailer!.
Qed.

Lemma proof_of_OSMboxPend_which_implies_wit_14 : OSMboxPend_which_implies_wit_14.
Proof.
  left; intros.
  destruct PreH1 as [Hentry Hresult].
  pose proof (q_pend_cleanup_continuations_merge external platform environment saved_local sg resumed
    cleaning resume_tid node Hentry) as Hmerge.
  cbn [task_storage.tcb_cell task_storage.tcb_field_address] in Hmerge.
  rewrite <- PreH3 in Hmerge.
  unfold mbox_pend_masked_frame, q_pend_masked_frame.
  sep_apply_l_atomic Hmerge.
  Exists (message_pend_cleanup_state sg cleaning resume_tid node).
  unfold mbox_pend_restore_input, mbox_pend_masked_frame, q_pend_masked_frame.
  entailer!.
Qed.

