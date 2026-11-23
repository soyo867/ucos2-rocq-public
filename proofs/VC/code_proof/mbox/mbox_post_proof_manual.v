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
From Ucos2Verify.VC.code.mbox Require Import mbox_post_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_post_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxPost_entail_wit_1 : OSMboxPost_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  entailer!; unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize in *; lia.
Qed.

Lemma proof_of_OSMboxPost_entail_wit_3 : OSMboxPost_entail_wit_3.
Proof.
  left; intros.
  Exists active_2 acquired_3 observed_2 current_3 m_2.
  rewrite <- PreH4, PreH1; entailer!.
Qed.

Lemma proof_of_OSMboxPost_return_wit_1 : OSMboxPost_return_wit_1.
Proof.
  left; intros; apply mbox_post_nonschedule_return; exact PreH2.
Qed.

Lemma proof_of_OSMboxPost_return_wit_2 : OSMboxPost_return_wit_2.
Proof.
  left; intros; rewrite <- PreH3.
  apply mbox_post_nonschedule_return; exact PreH28.
Qed.

Lemma proof_of_OSMboxPost_return_wit_3 : OSMboxPost_return_wit_3.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  apply mbox_post_sched_return; assumption.
Qed.

Lemma proof_of_OSMboxPost_return_wit_4 : OSMboxPost_return_wit_4.
Proof.
  left; intros.
  pose proof PreH10 as [[_ [_ [_ [_ [Hlayout _]]]]] _].
  pose proof (mbox_post_type_merge environment critical saved_local sg caller
    mask before eid PreH11) as Hmerge.
  rewrite <- PreH6 in Hmerge.
  rewrite (Hlayout pe), Hmerge.
  apply mbox_post_closed_return; [|exact PreH21].
  exists caller, before, false; split.
  - unfold mbox_post_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) PreH7),
      (proj2 (Z.eqb_neq _ _) PreH8),
      (proj2 (Z.eqb_neq _ _) PreH1); auto.
  - split; reflexivity.
Qed.

Lemma proof_of_OSMboxPost_return_wit_5 : OSMboxPost_return_wit_5.
Proof.
  left; intros.
  assert (Hpe : pe <> 0) by congruence.
  assert (Hmessage : message = 0) by congruence.
  apply mbox_post_closed_return; [|exact PreH9].
  exists caller, before, false; split.
  - unfold mbox_post_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) Hpe), Hmessage; cbn; auto.
  - split; reflexivity.
Qed.

Lemma proof_of_OSMboxPost_return_wit_6 : OSMboxPost_return_wit_6.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by congruence.
  apply mbox_post_closed_return; [|exact PreH8].
  exists caller, before, false; split.
  - unfold mbox_post_prefix_program; rewrite Hpe; cbn; auto.
  - split; reflexivity.
Qed.

Lemma proof_of_OSMboxPost_partial_solve_wit_5_pure : OSMboxPost_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hzero; apply PreH1; rewrite Hzero; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPost_partial_solve_wit_6_pure : OSMboxPost_partial_solve_wit_6_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH29.
  decompose [and] PreH29; entailer!.
Qed.

Lemma proof_of_OSMboxPost_partial_solve_wit_11_pure : OSMboxPost_partial_solve_wit_11_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired current)).
  Intros.
  rewrite unsigned_last_nbits_eq in PreH1.
  - entailer!.
  - change (0 <= q_post_group acquired current <= 255) in H.
    change (0 <= q_post_group acquired current < 4294967296); lia.
Qed.

Lemma proof_of_OSMboxPost_which_implies_wit_1 : OSMboxPost_which_implies_wit_1.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    Hpe Hmessage Hprofile Hvalid Hinput.
  pose proof Hinput as Hreadable.
  destruct Hreadable as [Hzero|[Hzero|[_ [Haddr [Hid Hrest]]]]]; try contradiction.
  destruct Hprofile as [[_ [_ [_ [_ [Htype Hptr]]]]] Hlayout].
  rewrite Htype, Haddr.
  sep_apply_l_atomic (mbox_post_type_split environment critical saved_local sg caller mask
    before pe message eid Hvalid Hpe Hmessage Hinput).
  entailer!.
Qed.

Lemma proof_of_OSMboxPost_which_implies_wit_2 : OSMboxPost_which_implies_wit_2.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    Haddr Hpe Hmessage Hid Hprofile Hvalid Hinput Htype.
  destruct Hprofile as [[_ [_ [_ [_ [Harrow Hptr]]]]] Hlayout].
  subst pe; rewrite Harrow.
  sep_apply_l_atomic (mbox_post_type_merge environment critical saved_local sg caller mask before eid Hvalid).
  unfold mbox_post_save_pre; entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_3 : OSMboxPost_which_implies_wit_3.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment pevent cpu_sr
    Haddr Hid Hprofile.
  unfold mbox_post_save_result; Intros active acquired observed current.
  pose proof H as [Hsave [_ [_ [_ [_ [_ [_ [Hcurrent _]]]]]]]].
  pose proof (proj2 Hprofile eid Hid) as [_ [Hgrp Htbl]].
  rewrite Haddr, Hgrp.
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired acquired).
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid current Hcurrent).
  Intros.
  Exists active acquired observed current.
  unfold mbox_post_group_context; entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_4 : OSMboxPost_which_implies_wit_4.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    current observed acquired active pevent cpu_sr Haddr Hnonzero.
  unfold mbox_post_group_context; Intros.
  destruct H as [Hacquire Hprofile].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Hevent [Hid [Hobserved
    [Hobservedtype [Hcurrent [Htype Hgen]]]]]]]]].
  pose proof (proj2 Hprofile eid Hid) as Hlayout.
  pose proof Hlayout as [_ [Hgrp Htbl]].
  rewrite Haddr, Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired eid current (proj1 Hsave) Hcurrent).
  sep_apply_l_atomic (mbox_post_wake_split sg acquired eid current (proj1 Hsave)
    Hcurrent Htype Hnonzero Hlayout).
  Intros tid old.
  Exists active acquired observed current tid old.
  unfold mbox_post_wake_context; entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_5 : OSMboxPost_which_implies_wit_5.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    priority old tid current observed acquired active cpu_sr Hpe.
  unfold mbox_post_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Hnonzero Hentry]]].
  pose proof Hacquire as [Hsave [Hpe' [Hmessage [Hevent [Hid [Hobserved
    [Hobservedtype [Hcurrent [Htype Hgen]]]]]]]]].
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (mbox_post_wake_merge sg acquired eid current tid old message priority
    (proj1 Hsave) Hcurrent Htype Hentry).
  Intros after.
  match goal with Hresult : mbox_post_wake_result _ _ _ _ _ _ |- _ =>
    pose proof Hresult as Hwakeres end.
  destruct (event_wake_decompose sg acquired eid current PendMbox message PendOK priority after
    (proj1 Hsave) Hcurrent ltac:(rewrite Htype; reflexivity) Hnonzero Hwakeres)
    as [head [tail [actualold [Hlist [Hlookup [Hpriority [Hafter [Hvalid Hlast]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  rewrite Hlist in Hhead; cbn in Hhead; injection Hhead as Heq; subst head.
  assert (actualold = old) by congruence; subst actualold; subst after.
  pose proof (mbox_post_acquire_original_type environment critical sg caller active mask cpu_sr
    pe message before acquired eid observed current Hacquire) as Hbeforetype.
  assert (Heffect : mbox_post_effect sg eid message acquired 0 1
    (cross_module_invariants.event_wake_state sg acquired eid current tid old PendMbox message PendOK)).
  { exists true; split; [reflexivity|].
    eapply mbox_post_wake_critical; eassumption. }
  sep_apply_l_atomic (mbox_post_mask_frame_wake_update environment critical saved_local sg active cpu_sr
    acquired acquired eid current tid old message Hold).
  Exists active acquired (cross_module_invariants.event_wake_state sg acquired eid current tid old PendMbox message PendOK).
  unfold mbox_post_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired
    (cross_module_invariants.event_wake_state sg acquired eid current tid old PendMbox message PendOK)).
  entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_6 : OSMboxPost_which_implies_wit_6.
Proof.
  right; intros.
  apply mbox_post_restored_schedule_pre; assumption.
Qed.

Lemma proof_of_OSMboxPost_which_implies_wit_7 : OSMboxPost_which_implies_wit_7.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    current observed acquired active pevent cpu_sr Haddr Hzero.
  unfold mbox_post_group_context; Intros.
  destruct H as [Hacquire Hprofile].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Hevent [Hid [Hobserved
    [Hobservedtype [Hcurrent [Htype Hgen]]]]]]]]].
  pose proof (proj2 Hprofile eid Hid) as [_ [Hgrp Htbl]].
  pose proof (proj1 Hprofile) as [_ [_ [_ [_ [Htypearrow Hptr]]]]].
  rewrite Haddr, Hgrp, Hptr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired eid current (proj1 Hsave) Hcurrent).
  destruct (mbox_post_current_message sg acquired eid current (proj1 Hsave) Hcurrent Htype Hzero)
    as [m [Hm [Hempty Hconsistent]]].
  sep_apply_l_atomic (mbox_post_message_split sg acquired eid current m Hcurrent Htype Hm).
  Intros.
  Exists active acquired observed current m.
  unfold mbox_post_message_context; entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_8 : OSMboxPost_which_implies_wit_8.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    m current observed acquired active cpu_sr Hfull.
  unfold mbox_post_message_context; Intros.
  destruct H as [Hacquire [Hprofile [Hzero [Hm [Hempty Hconsistent]]]]].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Hevent [Hid [Hobserved
    [Hobservedtype [Hcurrent [Htype Hgen]]]]]]]]].
  pose proof (proj1 Hprofile) as [_ [_ [_ [_ [Htypearrow Hptr]]]]].
  rewrite Hptr, Hevent.
  sep_apply_l_atomic (mbox_post_message_merge_original sg acquired eid current m
    (proj1 Hsave) Hcurrent Htype Hm).
  pose proof (mbox_post_acquire_original_type environment critical sg caller active mask cpu_sr
    pe message before acquired eid observed current Hacquire) as Hbeforetype.
  assert (Heffect : mbox_post_effect sg eid message acquired 20 0 acquired).
  { exists false; split; [reflexivity|].
    eapply mbox_post_full_critical; eassumption. }
  pose proof (proj1 Hsave) as Hvalid.
  Exists active acquired.
  unfold mbox_post_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired acquired).
  entailer!.
Qed.


Lemma proof_of_OSMboxPost_which_implies_wit_9 : OSMboxPost_which_implies_wit_9.
Proof.
  right; intros message pe eid before mask caller sg critical saved_local environment
    m current observed acquired active cpu_sr Hptrzero.
  unfold mbox_post_message_context; Intros.
  destruct H as [Hacquire [Hprofile [Hzero [Hm [Hempty Hconsistent]]]]].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [Hevent [Hid [Hobserved
    [Hobservedtype [Hcurrent [Htype Hgen]]]]]]]]].
  pose proof (proj1 Hprofile) as [_ [_ [_ [_ [Htypearrow Hptr]]]]].
  rewrite Hptr, Hevent.
  sep_apply_l_atomic (mbox_post_message_merge_updated sg acquired eid current message
    (proj1 Hsave) Hcurrent Htype Hempty Hmessage).
  pose proof (mbox_post_acquire_original_type environment critical sg caller active mask cpu_sr
    pe message before acquired eid observed current Hacquire) as Hbeforetype.
  pose proof (mbox_post_store_preserves_validity sg acquired eid current message
    (proj1 Hsave) Hcurrent Htype Hempty Hmessage) as Hvalid.
  assert (Heffect : mbox_post_effect sg eid message acquired 0 0
    (mbox_post_store_state acquired eid current message)).
  { exists false; split; [reflexivity|].
    eapply mbox_post_store_critical; eassumption. }
  sep_apply_l_atomic (q_post_mask_frame_event_update environment critical saved_local sg active cpu_sr
    acquired acquired (mbox_post_store_state acquired eid current message) eq_refl).
  Exists active acquired (mbox_post_store_state acquired eid current message).
  unfold mbox_post_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired
    (mbox_post_store_state acquired eid current message)).
  entailer!.
Qed.


