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
From Ucos2Verify.VC.code.mbox Require Import mbox_post_opt_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_post_opt_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_opt_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxPostOpt_entail_wit_1 : OSMboxPostOpt_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("opt")) opt_pre).
  Intros.
  rename H into Hrange.
  change (0 <= opt_pre <= 255) in Hrange.
  entailer!; lia.
Qed.

Lemma proof_of_OSMboxPostOpt_entail_wit_2 : OSMboxPostOpt_entail_wit_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  Intros.
  rename H into Hrange.
  change (0 <= event_slot_type_value (EventState before) eid <= 255) in Hrange.
  entailer!; lia.
Qed.

Lemma proof_of_OSMboxPostOpt_entail_wit_8 : OSMboxPostOpt_entail_wit_8.
Proof.
  left; intros.
  Exists active_2 acquired_3 observed_2 current_3 m_2.
  rewrite PreH4, PreH27, PreH1.
  entailer!.
  rewrite <- PreH4; exact PreH32.
Qed.

Lemma proof_of_OSMboxPostOpt_return_wit_1 : OSMboxPostOpt_return_wit_1.
Proof.
  left; intros.
  apply mbox_post_opt_nonschedule_return; exact PreH2.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_2 : OSMboxPostOpt_return_wit_2.
Proof.
  left; intros.
  rewrite <- PreH3.
  apply mbox_post_opt_nonschedule_return; exact PreH31.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_3 : OSMboxPostOpt_return_wit_3.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  eapply mbox_post_opt_sched_return; eassumption.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_4 : OSMboxPostOpt_return_wit_4.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  eapply mbox_post_opt_sched_return; eassumption.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_5 : OSMboxPostOpt_return_wit_5.
Proof.
  left; intros.
  rewrite <- PreH3.
  unfold mbox_post_opt_schedule_flag.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  apply mbox_post_opt_nonschedule_return; exact PreH8.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_6 : OSMboxPostOpt_return_wit_6.
Proof.
  left; intros.
  unfold mbox_post_opt_schedule_flag.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  apply mbox_post_opt_nonschedule_return; exact PreH6.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_7 : OSMboxPostOpt_return_wit_7.
Proof.
  left; intros.
  pose proof (proj1 PreH8) as [_ [_ [_ [_ [Htype_address _]]]]].
  pose proof (mbox_post_type_merge environment critical saved_local sg caller mask before eid PreH9) as Hmerge.
  rewrite <- PreH4 in Hmerge.
  rewrite Htype_address, Hmerge.
  apply mbox_post_opt_closed_return; [|exact PreH24].
  exists caller, before, false; split; [|split; reflexivity].
  unfold mbox_post_opt_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) PreH5), (proj2 (Z.eqb_neq _ _) PreH6),
    (proj2 (Z.eqb_neq _ _) PreH1).
  split; reflexivity.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_8 : OSMboxPostOpt_return_wit_8.
Proof.
  left; intros.
  assert (Hpe : pe <> 0) by congruence.
  assert (Hmessage : message = 0) by congruence.
  apply mbox_post_opt_closed_return; [|exact PreH14].
  exists caller, before, false; split; [|split; reflexivity].
  unfold mbox_post_opt_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), Hmessage; cbn.
  split; reflexivity.
Qed. 

Lemma proof_of_OSMboxPostOpt_return_wit_9 : OSMboxPostOpt_return_wit_9.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by congruence.
  apply mbox_post_opt_closed_return; [|exact PreH13].
  exists caller, before, false; split; [|split; reflexivity].
  unfold mbox_post_opt_prefix_program; rewrite Hpe; cbn.
  split; reflexivity.
Qed. 

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_5_pure : OSMboxPostOpt_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hzero; apply PreH2; rewrite Hzero; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_6_pure : OSMboxPostOpt_partial_solve_wit_6_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group state node <> 0).
  { intro Hzero; apply PreH1; rewrite Hzero; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_7_pure : OSMboxPostOpt_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses,
    sched_new_spec.sched_new_global_addresses in PreH10.
  entailer!; tauto.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_9_pure : OSMboxPostOpt_partial_solve_wit_9_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)).
  Intros.
  rename H into Hrange.
  change (0 <= q_post_group state node <= 255) in Hrange.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group state node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_10_pure : OSMboxPostOpt_partial_solve_wit_10_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hzero; apply PreH2; rewrite Hzero; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_11_pure : OSMboxPostOpt_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses,
    sched_new_spec.sched_new_global_addresses in PreH33.
  entailer!; tauto.
Qed.

Lemma proof_of_OSMboxPostOpt_partial_solve_wit_19_pure : OSMboxPostOpt_partial_solve_wit_19_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired current)).
  Intros.
  rename H into Hrange.
  change (0 <= q_post_group acquired current <= 255) in Hrange.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group acquired current < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_1 : OSMboxPostOpt_which_implies_wit_1.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment
    Hpe Hmessage Hprofile Hvalid Hinput.
  pose proof Hinput as [Hzero|[Hzero|[_ [Haddr [Hid Hrest]]]]]; try contradiction.
  assert (Htype : forall p, (&(p # "os_event" ->ₛ "OSEventType")) = p + OSEventType_off).
  { unfold mbox_post_profile, mbox_accept_profile in Hprofile; tauto. }
  subst pe; rewrite Htype.
  sep_apply_l_atomic (mbox_post_type_split environment critical saved_local sg caller mask before
    (event_addr sg eid) message eid Hvalid Hpe Hmessage Hinput).
  entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_2 : OSMboxPostOpt_which_implies_wit_2.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment
    Haddr Hpe Hmessage Hid Hprofile Hvalid Hinput Hkind.
  assert (Htype : forall p, (&(p # "os_event" ->ₛ "OSEventType")) = p + OSEventType_off).
  { unfold mbox_post_profile, mbox_accept_profile in Hprofile; tauto. }
  subst pe; rewrite Htype.
  sep_apply_l_atomic (mbox_post_type_merge environment critical saved_local sg caller mask before eid Hvalid).
  unfold mbox_post_save_pre; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_3 : OSMboxPostOpt_which_implies_wit_3.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment pevent saved
    Haddr Hid Hprofile.
  subst pevent; rewrite (mbox_post_profile_group_address__resource_transitions sg eid Hprofile Hid).
  unfold mbox_post_save_result; Intros active acquired observed current.
  pose proof H as [_ [_ [_ [_ [_ [_ [_ [Hnode Hrest]]]]]]]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid current Hnode).
  Intros; Exists active acquired observed current.
  unfold mbox_post_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_4 : OSMboxPostOpt_which_implies_wit_4.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment
    initial observed acquired active pevent saved Haddr Hgroup.
  sep_apply_l_atomic (mbox_post_opt_loop_start environment critical saved_local sg caller active mask saved
    pe message before acquired eid observed initial Hgroup).
  Exists active acquired observed initial acquired initial; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_5 : OSMboxPostOpt_which_implies_wit_5.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment
    node state initial observed acquired active pevent saved Haddr Hgroup.
  sep_apply_l_atomic (mbox_post_opt_loop_context_profile__resource_transitions environment critical
    saved_local sg caller active mask saved pe before acquired eid observed initial message state node).
  Intros.
  subst pevent; rewrite (mbox_post_profile_group_address__resource_transitions sg eid (proj1 H) (proj2 H)).
  rewrite (mbox_post_opt_loop_wake_split environment critical saved_local sg caller active mask saved pe
    before acquired eid observed initial message state node Hgroup).
  Intros tid old; Exists active acquired observed initial state node tid old; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_6 : OSMboxPostOpt_which_implies_wit_6.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment priority old tid
    node state initial observed acquired active pevent saved Haddr.
  rewrite (mbox_post_opt_loop_wake_merge environment critical saved_local sg caller active mask saved pe
    before acquired eid observed initial message state node tid old priority).
  Intros after next.
  sep_apply_l_atomic (mbox_post_opt_loop_context_profile__resource_transitions environment critical
    saved_local sg caller active mask saved pe before acquired eid observed initial message after next).
  Intros.
  subst pevent; rewrite (mbox_post_profile_group_address__resource_transitions sg eid (proj1 H) (proj2 H)).
  Exists active acquired observed initial after next; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_7 : OSMboxPostOpt_which_implies_wit_7.
Proof.
  left; intros options message pe eid before mask caller sg critical saved_local environment node state
    initial observed acquired active saved Haddr Hpe Hbroadcast Hzero.
  sep_apply_l_atomic (mbox_post_opt_loop_context_profile__resource_transitions environment critical
    saved_local sg caller active mask saved pe before acquired eid observed initial message state node).
  Intros.
  rewrite Haddr at 2.
  rewrite (mbox_post_profile_group_address__resource_transitions sg eid (proj1 H) (proj2 H)).
  Exists active acquired state.
  apply (mbox_post_opt_loop_restore environment critical saved_local sg caller active mask saved pe
    before acquired eid observed initial message options state node Hbroadcast Hzero).
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_8 : OSMboxPostOpt_which_implies_wit_8.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment current observed
    acquired active pevent saved Haddr Hgroup.
  unfold mbox_post_group_context; Intros.
  destruct H as [Hacquire Hprofile].
  pose proof Hacquire as [[Hvalid Hsave] [_ [_ [_ [Hid [_ [_ [Hnode [Htype Hg]]]]]]]]].
  subst pevent; rewrite (mbox_post_profile_group_address__resource_transitions sg eid Hprofile Hid).
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired eid current Hvalid Hnode).
  sep_apply_l_atomic (mbox_post_wake_split sg acquired eid current Hvalid Hnode Htype Hgroup
    (proj2 Hprofile eid Hid)).
  Intros tid old; Exists active acquired observed current tid old.
  unfold mbox_post_wake_context, q_post_sched_group, q_post_sched_rows; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_9 : OSMboxPostOpt_which_implies_wit_9.
Proof.
  left; intros options message pe eid before mask caller sg critical saved_local environment priority old tid
    current observed acquired active saved Hpe Hsingle.
  unfold mbox_post_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup Hentry]]].
  pose proof Hacquire as [Hsave [_ [Hmessage [_ [_ [_ [_ [Hnode [Htype Hg]]]]]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (mbox_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (mbox_post_wake_merge sg acquired eid current tid old message priority Hvalid Hnode Htype Hentry).
  Intros after.
  pose proof (mbox_post_opt_single_wake_critical sg acquired eid current message options priority after
    Hnode Hgroup Hsingle H) as Hstep.
  destruct (mbox_post_opt_wake_decompose sg acquired eid current message priority after
    Hvalid Hnode Htype Hgroup H)
    as [selected [tail [previous [Hlist [Hold [Hpriority [Hafter [Hafter_valid Hafter_node]]]]]]]].
  subst after.
  sep_apply_l_atomic (mbox_post_mask_frame_wake_update environment critical saved_local sg active saved
    acquired acquired eid current selected previous message Hold).
  assert (Heffect : mbox_post_opt_effect sg eid message options acquired 0
    (mbox_post_opt_schedule_flag options)
    (Ucos2Verify.lib.cross_module_invariants.event_wake_state sg acquired eid current selected previous
      Ucos2Verify.lib.task_status.PendMbox message Ucos2Verify.lib.task_status.PendOK)).
  { exists (Z.eqb (Z.land options 4) 0); split; [reflexivity|exact Hstep]. }
  Exists active acquired (Ucos2Verify.lib.cross_module_invariants.event_wake_state sg acquired eid current
    selected previous Ucos2Verify.lib.task_status.PendMbox message Ucos2Verify.lib.task_status.PendOK).
  unfold mbox_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_10 : OSMboxPostOpt_which_implies_wit_10.
Proof.
  left; intros.
  unfold mbox_post_opt_schedule_flag; rewrite PreH1.
  apply mbox_post_opt_restored_schedule_pre; exact PreH2.
Qed. 

Lemma proof_of_OSMboxPostOpt_which_implies_wit_11 : OSMboxPostOpt_which_implies_wit_11.
Proof.
  left; intros message pe eid before mask caller sg critical saved_local environment current observed
    acquired active pevent saved Haddr Hgroup.
  unfold mbox_post_group_context; Intros.
  destruct H as [Hacquire Hprofile].
  pose proof Hacquire as [[Hvalid Hsave] [_ [_ [_ [Hid [_ [_ [Hnode [Htype Hg]]]]]]]]].
  assert (Hptr : forall p, (&(p # "os_event" ->ₛ "OSEventPtr")) = p + OSEventPtr_off).
  { unfold mbox_post_profile, mbox_accept_profile in Hprofile; tauto. }
  subst pevent; rewrite (mbox_post_profile_group_address__resource_transitions sg eid Hprofile Hid), Hptr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired eid current Hvalid Hnode).
  destruct (mbox_post_current_message sg acquired eid current Hvalid Hnode Htype Hgroup)
    as [m [Hm [Hempty Hconsistent]]].
  sep_apply_l_atomic (mbox_post_message_split sg acquired eid current m Hnode Htype Hm).
  Intros; Exists active acquired observed current m.
  unfold mbox_post_message_context; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_12 : OSMboxPostOpt_which_implies_wit_12.
Proof.
  left; intros options message pe eid before mask caller sg critical saved_local environment m current
    observed acquired active saved Hfull.
  unfold mbox_post_message_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hm [Hempty Hconsistent]]]]].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Haddr [_ [_ [_ [Hnode [Htype Hg]]]]]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (mbox_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  assert (Hptr : forall p, (&(p # "os_event" ->ₛ "OSEventPtr")) = p + OSEventPtr_off).
  { unfold mbox_post_profile, mbox_accept_profile in Hprofile; tauto. }
  rewrite Hptr, Haddr.
  sep_apply_l_atomic (mbox_post_message_merge_original sg acquired eid current m Hvalid Hnode Htype Hm).
  assert (Heffect : mbox_post_opt_effect sg eid message options acquired 20 0 acquired).
  { exists false; split; [reflexivity|]. eapply mbox_post_opt_full_critical; eassumption. }
  Exists active acquired; unfold mbox_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSMboxPostOpt_which_implies_wit_13 : OSMboxPostOpt_which_implies_wit_13.
Proof.
  left; intros options message pe eid before mask caller sg critical saved_local environment m current
    observed acquired active saved Hempty_ptr.
  unfold mbox_post_message_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hm [Hempty Hconsistent]]]]].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Haddr [_ [_ [_ [Hnode [Htype Hg]]]]]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (mbox_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  assert (Hptr : forall p, (&(p # "os_event" ->ₛ "OSEventPtr")) = p + OSEventPtr_off).
  { unfold mbox_post_profile, mbox_accept_profile in Hprofile; tauto. }
  rewrite Hptr, Haddr.
  sep_apply_l_atomic (mbox_post_message_merge_updated sg acquired eid current message Hvalid Hnode Htype Hempty Hmessage).
  assert (Hafter_valid : UCOS2_state_inv sg (mbox_post_store_state acquired eid current message)).
  { apply mbox_post_store_preserves_validity; assumption. }
  assert (Heffect : mbox_post_opt_effect sg eid message options acquired 0 0
    (mbox_post_store_state acquired eid current message)).
  { exists false; split; [reflexivity|]. eapply mbox_post_opt_store_critical; eassumption. }
  assert (Hframe : q_post_mask_frame environment critical saved_local sg active saved acquired acquired =
    q_post_mask_frame environment critical saved_local sg active saved acquired
      (mbox_post_store_state acquired eid current message)).
  { destruct active; reflexivity. }
  rewrite Hframe.
  Exists active acquired (mbox_post_store_state acquired eid current message).
  unfold mbox_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

