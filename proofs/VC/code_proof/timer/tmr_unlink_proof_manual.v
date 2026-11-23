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
From Ucos2Verify.VC.code.timer Require Import tmr_unlink_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_unlink_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmr_Unlink_entail_wit_1 : OSTmr_Unlink_entail_wit_1.
Proof.
  right; intros.
  entailer!.
  apply IntLib.unsigned_last_nbits_eq.
  pose proof (Z.rem_bound_pos match_time_raw_spec 7 ltac:(lia) ltac:(lia)).
  cbn; lia.
Qed. 

Lemma proof_of_OSTmr_Unlink_entail_wit_2 : OSTmr_Unlink_entail_wit_2.
Proof.
  left; intros.
  unfold tmr_unlink_wheel_size in PreH4.
  change (CNotation.sizeof_alias_type "os_tmr_wheel" = 8) in PreH4.
  change (sizeof("os_tmr_wheel")) with (CNotation.sizeof_alias_type "os_tmr_wheel").
  rewrite PreH4, PreH15.
  replace (Z.rem match_time_raw_spec 7 * 8) with (8 * Z.rem match_time_raw_spec 7) by lia.
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_return_wit_1 : OSTmr_Unlink_return_wit_1.
Proof.
  left; intros.
  unfold tmr_unlink_raw_post, tmr_unlink_neighbor_post,
    tmr_unlink_timer_field, tmr_unlink_wheel_field, tmr_unlink_spoke_addr.
  rewrite Z.rem_mod_nonneg by lia.
  unfold IntLib.unsigned_last_nbits, kernel_resources.kernel_u16.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [|contradiction].
  destruct (Z.eq_dec next_raw_spec 0); [contradiction|].
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_return_wit_2 : OSTmr_Unlink_return_wit_2.
Proof.
  left; intros.
  unfold tmr_unlink_raw_post, tmr_unlink_neighbor_post,
    tmr_unlink_timer_field, tmr_unlink_wheel_field, tmr_unlink_spoke_addr.
  rewrite Z.rem_mod_nonneg by lia.
  unfold IntLib.unsigned_last_nbits, kernel_resources.kernel_u16.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [|contradiction].
  destruct (Z.eq_dec next_raw_spec 0); [|contradiction].
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_return_wit_3 : OSTmr_Unlink_return_wit_3.
Proof.
  left; intros.
  unfold tmr_unlink_raw_post, tmr_unlink_neighbor_post,
    tmr_unlink_timer_field, tmr_unlink_wheel_field, tmr_unlink_spoke_addr.
  rewrite Z.rem_mod_nonneg by lia.
  unfold IntLib.unsigned_last_nbits, kernel_resources.kernel_u16.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [contradiction|].
  destruct (Z.eq_dec next_raw_spec 0); [contradiction|].
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_return_wit_4 : OSTmr_Unlink_return_wit_4.
Proof.
  left; intros.
  unfold tmr_unlink_raw_post, tmr_unlink_neighbor_post,
    tmr_unlink_timer_field, tmr_unlink_wheel_field, tmr_unlink_spoke_addr.
  rewrite Z.rem_mod_nonneg by lia.
  unfold IntLib.unsigned_last_nbits, kernel_resources.kernel_u16.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [contradiction|].
  destruct (Z.eq_dec next_raw_spec 0); [|contradiction].
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_which_implies_wit_1 : OSTmr_Unlink_which_implies_wit_1.
Proof.
  left; intros.
  unfold tmr_unlink_raw_pre.
  Intros.
  unfold tmr_unlink_timer_field, tmr_unlink_wheel_field, tmr_unlink_spoke_addr.
  rewrite Z.rem_mod_nonneg by lia.
  entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_which_implies_wit_2 : OSTmr_Unlink_which_implies_wit_2.
Proof.
  intros first_raw_spec prev_raw_spec next_raw_spec p_raw_spec PreH1.
  unfold tmr_unlink_neighbor_pre, tmr_unlink_timer_field.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [|contradiction].
  destruct (Z.eq_dec next_raw_spec 0).
  - Left; entailer!.
  - Right; entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_which_implies_wit_3 : OSTmr_Unlink_which_implies_wit_3.
Proof.
  intros first_raw_spec prev_raw_spec next_raw_spec p_raw_spec PreH1.
  unfold tmr_unlink_neighbor_pre, tmr_unlink_timer_field.
  destruct (Z.eq_dec first_raw_spec p_raw_spec); [contradiction|].
  destruct (Z.eq_dec next_raw_spec 0).
  - Right; entailer!.
  - Left; entailer!.
Qed. 

Lemma proof_of_OSTmr_Unlink_derive_configured_spec_by_raw_spec : OSTmr_Unlink_derive_configured_spec_by_raw_spec.
Proof.
  pre_process.
  rename R_configured_spec into R, i_configured_spec into i,
    s_configured_spec into s, sg_configured_spec into sg.
  rename H into Hlayout, H0 into Hprofile, H1 into Hinit,
    H2 into Hrunning, H3 into Hptmr, H4 into Hbase.
  unfold timer_inv; Intros; rename H into Hvalid.
  pose proof Hprofile as [Henabled [Hnames [Hcapacity [Hwheel_size [Hpool Hwheel_region]]]]].
  pose proof Hlayout as [_ [_ [_ [_ [Hfirst_addr [Hentries_addr Hsizeof]]]]]].
  rewrite (timer_initialized_configured_rep_eq sg s Henabled Hinit).
  pose proof (proj1 (timer_initialized_configuration_iff sg s Henabled Hinit) Hvalid) as Hstate.
  destruct Hrunning as [t [Ht Hrunning]].
  destruct (valid_timer_state_running_position sg s i t Hstate Ht Hrunning)
    as [n [row [old [Hi [Hrow [Hin Hn]]]]]].
  pose proof Hstate as [_ [Hwheel [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  pose proof Hwheel as [_ [Hnd _]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  pose proof (tmr_unlink_profile_pool_region sg Hprofile) as Hpool_region.
  pose proof (tmr_unlink_profile_object_size sg Hprofile) as Hobject_size.
  assert (Haddress_bounds : forall j, In j row ->
    0 < timer_pool_addr sg j /\ timer_pool_addr sg j + 40 <= 4294967296).
  { intros j Hj.
    pose proof (timer_pool_addr_in_range sg j Hpool_region
      (timer_wheel_row_ids_in_range sg s n row j Hstate Hrow Hj)) as Hbounds.
    rewrite Hobject_size in Hbounds; exact Hbounds. }
  pose proof (Haddress_bounds i Hin) as Htarget_bounds.
  assert (Hnonnull : forall j, In j row -> timer_pool_addr sg j <> 0)
    by (intros j Hj; pose proof (Haddress_bounds j Hj); lia).
  destruct (Hused i t Ht) as [Hobject_valid _].
  pose proof (timer_used_image_eq sg s i t old Hstate Ht Hi) as Himage.
  assert (Hmatch_range : 0 <= timerImageMatch old < 4294967296).
  { rewrite Himage; cbn [timer_object_image].
    destruct Hobject_valid as [_ [_ [Hmatch _]]]; exact Hmatch. }
  assert (Hspoke : timer_spoke (osKernelConfig sg) (timerImageMatch old) = timerImageMatch old mod 7).
  { unfold timer_spoke, Ucos2Verify.lib.kernel_resources.kernel_u16; rewrite Hwheel_size.
    rewrite Z.mod_small; [reflexivity|pose proof (tmr_unlink_spoke_in_range (timerImageMatch old)); lia]. }
  assert (Hindex : Z.of_nat n = timerImageMatch old mod 7).
  { rewrite Hn, Hspoke, Z2Nat.id; [reflexivity|pose proof (tmr_unlink_spoke_in_range (timerImageMatch old)); lia]. }
  destruct (tmr_unlink_row_entries_decrease sg s n row i Hprofile Hstate Hrow Hin)
    as [Hentries_bounds Hentries].
  destruct (tmr_unlink_row_neighbor_facts__configured_refinement sg s n row i old Hprofile Hstate Hrow Hin Hi)
    as [Hneighbor_bounds [Hprev [Hnext Hdistinct]]].
  destruct (tmr_unlink_images_fields_split_merge__configured_refinement true sg (timerImages s) i old row
    Hlayout Hnames Hi Hprev Hnext Hdistinct) as [Fimages [Himages_pre Himages_post]].
  destruct (tmr_unlink_configured_successor sg s i Hprofile Hvalid Hinit
    (ex_intro _ t (conj Ht Hrunning))) as [post [Hstep [Hpost_valid Hpost_init]]].
  assert (Hnth : nth n (timerWheel s) nil = row) by (eapply nth_error_nth; exact Hrow).
  pose proof Hstep as Hstep_fields.
  unfold timer_unlink in Hstep_fields; rewrite Ht, Hi, <- Hn, Hnth in Hstep_fields.
  injection Hstep_fields as Hpost_eq.
  assert (Hpost_rep : timer_raw_rep sg post =
    store_map (fun j v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) v)
      (timer_wheel_unlink_images sg (timerImages s) i old row) **
    timer_wheel_rep_from sg (g_OSTmrWheelTbl sg)
      (timer_wheel_update (timerWheel s) n (remove Z.eq_dec i row)) **
    timer_globals_rep sg s).
  { rewrite <- Hpost_eq; reflexivity. }
  assert (Hfirst : timer_id_pointer sg (remove Z.eq_dec i row) =
    if Z.eq_dec (timer_id_pointer sg row) (timer_pool_addr sg i)
      then timerImageNext old else timer_id_pointer sg row).
  { apply tmr_unlink_row_first_after_remove__configured_refinement; try assumption.
    exact (proj1 (timer_wheel_row_node_pointers sg s n row i old Hwheel Hrow Hin Hi)). }
  assert (Hraw_bounds : tmr_unlink_wheel_size /\
    0 < timer_pool_addr sg i /\ timer_pool_addr sg i + 40 <= 4294967296 /\
    0 < g_OSTmrWheelTbl sg /\ g_OSTmrWheelTbl sg + 56 <= 4294967296 /\
    0 <= timerImageMatch old < 4294967296 /\ 0 <= Z.of_nat (List.length row) < 65536 /\
    tmr_unlink_neighbor_bounds (timer_pool_addr sg i) (timerImageNext old) (timerImagePrev old)
      (timer_id_pointer sg row)).
  { unfold kernel_region_valid in Hwheel_region; cbn in Hwheel_region; intuition lia. }
  set (Fraw := Fimages ** tmr_unlink_wheel_without_spoke sg (g_OSTmrWheelTbl sg) (timerWheel s) n **
    timer_globals_rep sg s ** R).
  Exists (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (timerImageMatch old)
    (timerImageNext old) (timerImagePrev old) (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw.
  assert (Hwand : emp |--
    tmr_unlink_raw_post (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (timerImageMatch old)
      (timerImageNext old) (timerImagePrev old) (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw
      -* (tmr_unlink_configured_post sg s i ** R)).
  {
    apply_sepcon_adjoint.
    unfold tmr_unlink_raw_post, tmr_unlink_configured_post, Fraw.
    Exists post.
    unfold timer_inv.
    rewrite (timer_initialized_configured_rep_eq sg post Henabled Hpost_init), Hpost_rep.
    entailer!.
    sepcon_right_assoc.
    sep_apply_r_atomic Himages_post; sepcon_right_assoc.
    sep_apply_r_atomic (tmr_unlink_wheel_merge_updated_spoke sg (timerWheel s) n row
      (remove Z.eq_dec i row) (g_OSTmrWheelTbl sg) Hrow).
    rewrite Hfirst_addr, Hentries_addr; unfold tmr_unlink_spoke_addr; rewrite <- Hindex, Hfirst.
    entailer!.
    rewrite Hentries; entailer!.
  }
  assert (Hpre : timer_raw_rep sg s ** R |--
    tmr_unlink_raw_pre (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (timerImageMatch old)
      (timerImageNext old) (timerImagePrev old) (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw).
  { unfold timer_raw_rep, timer_images_rep, tmr_unlink_raw_pre, Fraw.
    sep_apply_l_atomic Himages_pre.
    sep_apply_l_atomic (tmr_unlink_wheel_split_spoke sg (timerWheel s) n row (g_OSTmrWheelTbl sg) Hrow).
    rewrite Hfirst_addr, Hentries_addr; unfold tmr_unlink_spoke_addr; rewrite <- Hindex.
    entailer!.
  }
  sep_apply_l_atomic Hpre.
  entailer!.
Qed.
